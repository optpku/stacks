/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.Algebra.Category.Ring.Sheaf.Kummer
public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.AssociatedModule
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.EtaleCohomology.AffineCurve

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom] [IsAffine X.left]
variable (n : ℕ)
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasExt.{u + 1} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The unit of global sections obtained by evaluating a degree-zero Kummer class at the
small étale terminal object. -/
noncomputable def rootsH0GlobalUnit
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) : Γ(X.left, ⊤)ˣ :=
  let rootSection := Sheaf.H.equiv₀
    (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n)
    (MorphismProperty.Over.mkIdTerminal @Etale X.left) x
  let unitSection := CategoryTheory.Sheaf.unitsAddSheafUnit
    (smallCommStructureSheaf .etale X.left)
    ((kernel.ι (CategoryTheory.Sheaf.unitsNsmul
      (smallCommStructureSheaf .etale X.left) n)).hom.app
        (op (MorphismProperty.Over.mk ⊤ (𝟙 X.left) inferInstance)) rootSection)
  Units.map
    (ULift.ringEquiv : ULift.{u + 1, u} Γ(X.left, ⊤) ≃+* Γ(X.left, ⊤)).toMonoidHom
    unitSection

/-- For positive `n`, the scalar whose global section is the unit read out from a degree-zero
Kummer class. Positivity is needed on an affine curve, whose global units need not be constant. -/
noncomputable def rootsH0BaseValue
    [IsAlgClosed k] [IsReduced X.left] [ConnectedSpace X.left]
    (h_pos : 0 < n)
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) : k :=
  Function.invFun (Scheme.Hom.globalSectionsMap X.hom)
    (rootsH0GlobalUnit X n x).1

/-- Scalar descent is characterized by the global-sections image of the evaluated Kummer unit. -/
theorem rootsH0BaseValue_spec
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) (a : k) :
    Scheme.Hom.globalSectionsMap X.hom a = (rootsH0GlobalUnit X n x).1 ↔
      a = rootsH0BaseValue X n h_pos x := sorry

/-- The scalar descended from a degree-zero Kummer class is a unit in the base field. -/
theorem rootsH0BaseValue_isUnit
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    IsUnit (rootsH0BaseValue X n h_pos x) := sorry

/-- The deterministically constructed base-field unit satisfies the defining `n`th-root equation. -/
theorem rootsH0BaseUnit_pow
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    Units.mk0 (rootsH0BaseValue X n h_pos x)
      (rootsH0BaseValue_isUnit X n h_pos h_n x).ne_zero ∈ rootsOfUnity n k := sorry

/-- The forward comparison from degree-zero Kummer cohomology to base-field roots of unity. -/
noncomputable def rootsH0ComparisonFunction
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    Additive (rootsOfUnity n k) :=
  Additive.ofMul
    ⟨Units.mk0 (rootsH0BaseValue X n h_pos x)
        (rootsH0BaseValue_isUnit X n h_pos h_n x).ne_zero,
      rootsH0BaseUnit_pow X n h_pos h_n x⟩

/-- The degree-zero Kummer comparison preserves addition. -/
theorem rootsH0ComparisonFunction_add
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x y : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    rootsH0ComparisonFunction X n h_pos h_n (x + y) =
      rootsH0ComparisonFunction X n h_pos h_n x +
        rootsH0ComparisonFunction X n h_pos h_n y := sorry

/-- The degree-zero Kummer comparison is injective. -/
theorem rootsH0ComparisonFunction_injective
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Function.Injective (rootsH0ComparisonFunction X n h_pos h_n) := sorry

/-- The degree-zero Kummer comparison is surjective. -/
theorem rootsH0ComparisonFunction_surjective
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Function.Surjective (rootsH0ComparisonFunction X n h_pos h_n) := sorry

/-- Degree-zero étale cohomology with roots-of-unity coefficients is additively equivalent to
the roots of unity in the base field. -/
noncomputable def rootsH0
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    ((Sheaf.functorH X.left.smallEtaleTopology 0).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
      Additive (rootsOfUnity n k) where
  toFun := rootsH0ComparisonFunction X n h_pos h_n
  invFun := Function.invFun (rootsH0ComparisonFunction X n h_pos h_n)
  left_inv := Function.leftInverse_invFun
    (rootsH0ComparisonFunction_injective X n h_pos h_n)
  right_inv := Function.rightInverse_invFun
    (rootsH0ComparisonFunction_surjective X n h_pos h_n)
  map_add' := rootsH0ComparisonFunction_add X n h_pos h_n

/-- Mapping the underlying scalar of the degree-zero comparison back to global sections recovers
the evaluated Kummer unit. -/
theorem rootsH0_apply
    (h_pos : 0 < n) (h_n : IsUnit (n : k))
    (x : (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
      (smallCommStructureSheaf .etale X.left) n).H 0) :
    Scheme.Hom.globalSectionsMap X.hom
        ((rootsH0 X n h_pos h_n x : rootsOfUnity n k).1 : k) =
      (rootsH0GlobalUnit X n x).1 := sorry

/-- First étale cohomology with roots-of-unity coefficients is noncanonically equivalent to the
indicated finite product determined by a smooth projective compactification. -/
theorem rootsH1
    (Xbar : SchemeOverField k) [Curve Xbar] [Smooth Xbar.hom] [Projective Xbar.hom]
    (j : X.left ⟶ Xbar.left) [IsOpenImmersion j]
    (h_over : j ≫ Xbar.hom = X.hom)
    (g r : ℕ) (h_genus : AlgebraicGeometry.Curve.genus Xbar = g)
    (h_r : Nat.card {x : Xbar.left | x ∉ j.opensRange} = r)
    (h_finite : {x : Xbar.left | x ∉ j.opensRange}.Finite)
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) :
    Nonempty
      (((Sheaf.functorH X.left.smallEtaleTopology 1).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) ≃+
        (Fin (2 * g + r - 1) → ZMod n)) := sorry

/-- Étale cohomology with roots-of-unity coefficients vanishes in every degree at least two. -/
theorem roots_isZero
    (h_pos : 0 < n) (h_n : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) :
    IsZero
      ((Sheaf.functorH X.left.smallEtaleTopology q).obj
        (CategoryTheory.Sheaf.rootsOfUnityAddSheaf
          (smallCommStructureSheaf .etale X.left) n)) := sorry

end AlgebraicGeometry.EtaleCohomology.AffineCurve

end

end
