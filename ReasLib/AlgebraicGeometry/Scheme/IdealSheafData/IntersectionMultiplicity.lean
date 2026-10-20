module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.Topology.KrullDimension.ProperIntersection

/-!
# Intersection multiplicities of ideal-sheaf data

This module defines the local intersection multiplicity of two closed subschemes at a
generic component and records consequences of a multiplicity-one proper intersection.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} [Scheme.Regular X]

/-- The local intersection multiplicity at a generic component is the Euler multiplicity of
the two closed-subscheme stalks over their common ambient stalk. -/
noncomputable def intersectionMultiplicity (V W : X.IdealSheafData)
    (ξ : genericPoints (V ⊔ W).subscheme) : ℤ :=
  let iV := Scheme.IdealSheafData.inclusion (le_sup_left : V ≤ V ⊔ W)
  let iW := Scheme.IdealSheafData.inclusion (le_sup_right : W ≤ V ⊔ W)
  let hV := congrArg (fun f : (V ⊔ W).subscheme ⟶ X ↦ f.base ξ.1)
    (Scheme.IdealSheafData.inclusion_subschemeι (le_sup_left : V ≤ V ⊔ W))
  let hW := congrArg (fun f : (V ⊔ W).subscheme ⟶ X ↦ f.base ξ.1)
    (Scheme.IdealSheafData.inclusion_subschemeι (le_sup_right : W ≤ V ⊔ W))
  ∑ᶠ p : ℕ, (Int.negOnePow p : ℤ) *
    ((Module.length (X.presheaf.stalk (V.subschemeι (iV.base ξ.1)))
      (CategoryTheory.ModuleCat.Tor.obj p
        ((ModuleCat.restrictScalars
          (V.subschemeι.stalkMap (iV.base ξ.1)).hom).obj
            (ModuleCat.of (V.subscheme.presheaf.stalk (iV.base ξ.1))
              (V.subscheme.presheaf.stalk (iV.base ξ.1))))
        ((hV.trans hW.symm).symm ▸
          (ModuleCat.restrictScalars
            (W.subschemeι.stalkMap (iW.base ξ.1)).hom).obj
              (ModuleCat.of (W.subscheme.presheaf.stalk (iW.base ξ.1))
                (W.subscheme.presheaf.stalk (iW.base ξ.1)))))).toNat : ℤ)

/-- The scheme-level intersection multiplicity is the signed finsum of the lengths of the
Tor modules of the two transported closed-subscheme stalks. -/
theorem intersectionMultiplicity_apply (V W : X.IdealSheafData)
    (ξ : genericPoints (V ⊔ W).subscheme) :
    intersectionMultiplicity V W ξ =
      let iV := Scheme.IdealSheafData.inclusion (le_sup_left : V ≤ V ⊔ W)
      let iW := Scheme.IdealSheafData.inclusion (le_sup_right : W ≤ V ⊔ W)
      let hV := congrArg (fun f : (V ⊔ W).subscheme ⟶ X ↦ f.base ξ.1)
        (Scheme.IdealSheafData.inclusion_subschemeι (le_sup_left : V ≤ V ⊔ W))
      let hW := congrArg (fun f : (V ⊔ W).subscheme ⟶ X ↦ f.base ξ.1)
        (Scheme.IdealSheafData.inclusion_subschemeι (le_sup_right : W ≤ V ⊔ W))
      ∑ᶠ p : ℕ, (Int.negOnePow p : ℤ) *
        ((Module.length (X.presheaf.stalk (V.subschemeι (iV.base ξ.1)))
          (CategoryTheory.ModuleCat.Tor.obj p
            ((ModuleCat.restrictScalars
              (V.subschemeι.stalkMap (iV.base ξ.1)).hom).obj
                (ModuleCat.of (V.subscheme.presheaf.stalk (iV.base ξ.1))
                  (V.subscheme.presheaf.stalk (iV.base ξ.1))))
            ((hV.trans hW.symm).symm ▸
              (ModuleCat.restrictScalars
                (W.subschemeι.stalkMap (iW.base ξ.1)).hom).obj
                  (ModuleCat.of (W.subscheme.presheaf.stalk (iW.base ξ.1))
                    (W.subscheme.presheaf.stalk (iW.base ξ.1)))))).toNat : ℤ) := sorry

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : AlgebraicGeometry.SchemeOverField k) [Variety X]
  [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
  [Variety (Over.mk (V.subschemeι ≫ X.hom))]
  [Variety (Over.mk (W.subschemeι ≫ X.hom))]

/-- A multiplicity-one generic component of a proper intersection has local intersection
multiplicity one. -/
theorem intersectionMultiplicity_eq_one_of_componentMultiplicity_eq_one
    (hproper : Closeds.IntersectProperly V.support W.support)
    (ξ : genericPoints (V ⊔ W).subscheme)
    (hmult : componentMultiplicity (V ⊔ W) ξ = 1) :
    V.intersectionMultiplicity W ξ = 1 := sorry

/-- The left closed subvariety is smooth at a multiplicity-one generic component of a
proper intersection. -/
theorem leftSmoothAt_of_componentMultiplicity_eq_one
    (hproper : Closeds.IntersectProperly V.support W.support)
    (ξ : genericPoints (V ⊔ W).subscheme)
    (hmult : componentMultiplicity (V ⊔ W) ξ = 1) :
    (V.subschemeι ≫ X.hom).SmoothAt
      ((inclusion (le_sup_left : V ≤ V ⊔ W)).base ξ.1) := sorry

/-- The right closed subvariety is smooth at a multiplicity-one generic component of a
proper intersection. -/
theorem rightSmoothAt_of_componentMultiplicity_eq_one
    (hproper : Closeds.IntersectProperly V.support W.support)
    (ξ : genericPoints (V ⊔ W).subscheme)
    (hmult : componentMultiplicity (V ⊔ W) ξ = 1) :
    (W.subschemeι ≫ X.hom).SmoothAt
      ((inclusion (le_sup_right : W ≤ V ⊔ W)).base ξ.1) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
