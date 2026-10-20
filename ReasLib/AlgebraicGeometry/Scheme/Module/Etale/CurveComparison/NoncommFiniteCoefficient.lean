/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteCoefficientRestriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.NoncommGeometricSource

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace NoncommFiniteCoefficient
variable (R : Type (u + 1)) [Ring R] [Finite R]

/-- A finite ring, including the zero ring, has positive cardinality. -/
theorem card_pos : 0 < Nat.card R :=
  Nat.pos_of_ne_zero (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)

/-- The central integer-quotient map to an arbitrary finite ring. -/
def zmodHom : ZMod (Nat.card R) →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(Nat.card R : ℤ)}) (Int.castRingHom R)
    (by sorry)).comp (Int.quotientSpanNatEquivZMod (Nat.card R)).symm.toRingHom

/-- The actual lifted scalar homomorphism used by the existing roots coefficient. -/
def scalarHom : ActualRootsModule.Coeff.{u} (Nat.card R) →+* R :=
  (zmodHom R).comp ULift.ringEquiv.toRingHom

/-- Its image is central, because every element is the image of an integer. -/
theorem scalarHom_commute (a : ActualRootsModule.Coeff.{u} (Nat.card R)) (r : R) :
    scalarHom R a * r = r * scalarHom R a := by sorry

/-- Restrict the existing left R-action along the actual central scalar map. -/
abbrev modules := ModuleCat.restrictScalars (scalarHom R)

/-- Multiplication is linear over the central coefficient ring, on the actual
restricted module carrier. -/
def scalarModuleEnd (M : ModuleCat.{u + 1} R) (r : R) :
    (modules R).obj M ⟶ (modules R).obj M :=
  -- Local instance justification (defeq pin): expose precisely the chosen central scalar restriction.
  letI := Module.compHom M (scalarHom R)
  ModuleCat.ofHom (show (modules R).obj M →ₗ[ActualRootsModule.Coeff.{u} (Nat.card R)]
      (modules R).obj M from
    { toFun := fun m ↦ r • (show M from m)
      map_add' := by intros; exact smul_add _ _ _
      map_smul' := by sorry })

variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (modules R)]

/-- Same sections and restriction functions, now over the roots coefficient ring. -/
abbrev sheaves := sheafCompose Y.smallEtaleTopology (modules R)

variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))

/-- Intrinsic local-Hom dual into the actual roots sheaf, carrying its Tate twist. -/
abbrev dual := ActualLinearSheafHom.obj Y (ActualRootsModule.Coeff.{u} (Nat.card R))
  ((sheaves R Y).obj F) (ActualRootsModule.liftedSheaf Y (Nat.card R))

/-- Multiplication by r is A-linear AFTER central scalar restriction. It is
not falsely asserted to be an R-linear endomorphism of F. -/
def scalarEnd (r : R) : (sheaves R Y).obj F ⟶ (sheaves R Y).obj F :=
  ObjectProperty.homMk
    { app := fun U ↦ scalarModuleEnd R (F.obj.obj U) r
      naturality := by sorry }

/-- Right R-scalars act on intrinsic duals by actual source precomposition. -/
def dualScalarEnd (r : Rᵐᵒᵖ) : dual R Y F ⟶ dual R Y F :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun φ ↦ Functor.whiskerLeft (Over.forget U.unop).op
            (scalarEnd R Y F r.unop).hom ≫ φ
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- The multiplication order is the opposite-ring order, as required by precomposition. -/
def dualScalarAction : Rᵐᵒᵖ →+* End (dual R Y F) where
  toFun := dualScalarEnd R Y F
  map_zero' := by sorry
  map_one' := by sorry
  map_add' := by sorry
  map_mul' := by sorry

/-- Actual local evaluation at the identity of the slice site. -/
def evaluation (U : Y.Etaleᵒᵖ)
    (m : ((sheaves R Y).obj F).obj.obj U) (φ : (dual R Y F).obj.obj U) :
    (ActualRootsModule.liftedSheaf Y (Nat.card R)).obj.obj U :=
  (φ.app (op (Over.mk (𝟙 U.unop)))).hom m

/-- The displayed pairing is balanced for the LEFT source and RIGHT dual action. -/
theorem evaluation_balanced (U : Y.Etaleᵒᵖ) (r : R)
    (m : ((sheaves R Y).obj F).obj.obj U) (φ : (dual R Y F).obj.obj U) :
    evaluation R Y F U (((scalarEnd R Y F r).hom.app U).hom m) φ =
      evaluation R Y F U m (((dualScalarEnd R Y F (MulOpposite.op r)).hom.app U).hom φ) := by
  rfl

end NoncommFiniteCoefficient
