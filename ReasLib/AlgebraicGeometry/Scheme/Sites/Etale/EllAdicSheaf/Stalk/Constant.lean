/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Algebra.Module.ULift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk

/-!
# Coordinates on the stalk of the constant adic sheaf

Stage coordinates use the canonical fibre comparison for sheafification and
constant filtered colimits. Integral coordinates send a compatible system to
the padic Cauchy sequence of its least nonnegative residue representatives.
The reverse map is the limit lift of the residue maps. No inverse is selected
from an admitted existence or invertibility assertion.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open GrothendieckTopology.Point
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The actual fibre comparison on each constant stage. The sheafification
comparison used here has a proved inverse in mathlib. -/
def constantComponentStalkIso (x : GeometricPoint X) (n : ℕ) :
    (constant X ℓ).componentStalk x n ≅
      AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1)))) :=
  let Φ := GeometricPoint.toSmallEtalePoint x
  let A := AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1))))
  let P := (Functor.const X.Etaleᵒᵖ).obj A
  let D := (Functor.const Φ.fiber.Elementsᵒᵖ).obj A
  (Φ.presheafToSheafCompSheafFiberIso AddCommGrpCat.{u}).app P ≪≫
    (colimit.isColimit D).coconePointUniqueUpToIso (isColimitConstCocone _ A)

/-- Stage coordinates commute with every reduction map. -/
theorem constantComponentStalkIso_transition (x : GeometricPoint X)
    {i j : ℕ} (hij : i ≤ j) :
    ((constant X ℓ).componentStalkSystem x).transitionMap hij ≫
        (constantComponentStalkIso (ℓ := ℓ) x i).hom =
      (constantComponentStalkIso (ℓ := ℓ) x j).hom ≫
        zmodPowHom ℓ (Nat.succ_le_succ hij) := by
  sorry

/-- The integer representatives of the residues of an actual constant stalk. -/
def constantStalkResidueSeq (x : GeometricPoint X)
    (m : (constant X ℓ).stalk x) (n : ℕ) : ℤ :=
  ((constantComponentStalkIso (ℓ := ℓ) x n).hom
    ((constant X ℓ).stalk_π x n m)).down.val

/-- Compatibility of the residue projections makes their representatives a
padic Cauchy sequence. This is a property of the displayed sequence. -/
theorem constantStalkResidueSeq_isCauSeq (x : GeometricPoint X)
    (m : (constant X ℓ).stalk x) :
    IsCauSeq (padicNorm ℓ) (fun n ↦ (constantStalkResidueSeq x m n : ℚ)) := by
  sorry

/-- Integral coordinates are the quotient class of the explicit residue
Cauchy sequence, using `PadicInt.ofIntSeq`, not a selected limit. -/
def constantStalkToPadic (x : GeometricPoint X) :
    (constant X ℓ).stalk x →ₗ[ℤ_[ℓ]] ULift.{u} ℤ_[ℓ] where
  toFun m := ULift.up (PadicInt.ofIntSeq (constantStalkResidueSeq x m)
    (constantStalkResidueSeq_isCauSeq x m))
  map_add' := by sorry
  map_smul' := by sorry

/-- The cone of all reductions of a padic integer, in the actual constant
component stalks. -/
def constantPadicStalkCone (x : GeometricPoint X) :
    Cone ((constant X ℓ).componentStalkSystem x) where
  pt := AddCommGrpCat.of (ULift.{u} ℤ_[ℓ])
  π :=
    { app n :=
        AddCommGrpCat.ofHom
          ((AddEquiv.ulift.symm.toAddMonoidHom.comp
            (PadicInt.toZModPow (n.unop + 1)).toAddMonoidHom).comp
              AddEquiv.ulift.toAddMonoidHom) ≫
          (constantComponentStalkIso (ℓ := ℓ) x n.unop).inv
      naturality := by sorry }

/-- The reverse coordinate map is the universal lift of the explicit residue
cone; it does not invert a map using a bijectivity certificate. -/
def constantPadicToStalk (x : GeometricPoint X) :
    ULift.{u} ℤ_[ℓ] →ₗ[ℤ_[ℓ]] (constant X ℓ).stalk x where
  toFun := limit.lift _ (constantPadicStalkCone (ℓ := ℓ) x)
  map_add' := (limit.lift _ (constantPadicStalkCone (ℓ := ℓ) x)).hom.map_add
  map_smul' := by sorry

/-- Padic coordinates with both maps explicitly specified. -/
def constantStalkEquiv (x : GeometricPoint X) :
    (constant X ℓ).stalk x ≃ₗ[ℤ_[ℓ]] ULift.{u} ℤ_[ℓ] where
  toLinearMap := constantStalkToPadic x
  invFun := constantPadicToStalk x
  left_inv := by sorry
  right_inv := by sorry

/-- The forward coordinate is the displayed residue Cauchy class. -/
theorem constantStalkEquiv_apply (x : GeometricPoint X)
    (m : (constant X ℓ).stalk x) :
    constantStalkEquiv x m = ULift.up
      (PadicInt.ofIntSeq (constantStalkResidueSeq x m)
        (constantStalkResidueSeq_isCauSeq x m)) := rfl

/-- The inverse coordinate is exactly the explicit cone lift. -/
theorem constantStalkEquiv_symm_apply (x : GeometricPoint X) (a : ULift.{u} ℤ_[ℓ]) :
    (constantStalkEquiv x).symm a = constantPadicToStalk x a := rfl

/-- Coordinate reduction recovers the actual inverse-limit projection. -/
theorem constantStalkEquiv_residue (x : GeometricPoint X)
    (m : (constant X ℓ).stalk x) (n : ℕ) :
    PadicInt.toZModPow (n + 1) (constantStalkEquiv x m).down =
      ((constantComponentStalkIso (ℓ := ℓ) x n).hom
        ((constant X ℓ).stalk_π x n m)).down := by
  sorry

/-- Conversely, every projection of the reverse coordinate map is reduction
of the supplied padic integer. -/
theorem constantPadicToStalk_π (x : GeometricPoint X)
    (a : ULift.{u} ℤ_[ℓ]) (n : ℕ) :
    (constant X ℓ).stalk_π x n (constantPadicToStalk x a) =
      (constantComponentStalkIso (ℓ := ℓ) x n).inv
        (ULift.up (PadicInt.toZModPow (n + 1) a.down)) := by
  sorry

/-- Rational coordinates are scalar extension of the two explicit integral
coordinate maps followed by the tensor unit comparison. -/
def constantQellStalkEquiv (x : GeometricPoint X) :
    (constant X ℓ).qellStalk x ≃ₗ[ℚ_[ℓ]] ULift.{u} ℚ_[ℓ] :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ_[ℓ] ℚ_[ℓ])
    ((constantStalkEquiv (ℓ := ℓ) x).trans ULift.moduleEquiv)).trans
      ((TensorProduct.AlgebraTensorModule.rid ℤ_[ℓ] ℚ_[ℓ] ℚ_[ℓ]).trans
        ULift.moduleEquiv.symm)

/-- Rational coordinates on a pure tensor are multiplication by the integral
coordinate, embedded into the fraction field. -/
theorem constantQellStalkEquiv_tmul (x : GeometricPoint X) (a : ℚ_[ℓ])
    (m : (constant X ℓ).stalk x) :
    constantQellStalkEquiv x (a ⊗ₜ[ℤ_[ℓ]] m) =
      ULift.up (a * (algebraMap ℤ_[ℓ] ℚ_[ℓ]) (constantStalkEquiv x m).down) := by
  sorry

/-- The inverse rational coordinate sends a scalar to its pure tensor with
the integral unit section, using the explicit inverse integral comparison. -/
theorem constantQellStalkEquiv_symm_apply (x : GeometricPoint X)
    (a : ULift.{u} ℚ_[ℓ]) :
    (constantQellStalkEquiv x).symm a =
      a.down ⊗ₜ[ℤ_[ℓ]] (constantPadicToStalk (ℓ := ℓ) x (ULift.up 1)) := rfl

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
