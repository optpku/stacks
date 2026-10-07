module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Skeletal

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- Smooth proper curves of genus `g` over the field `k`, with global functions equal to `k`,
as an object property on `SchemeOverField k`. -/
def smoothProperOfGenus (k : Type u) [Field k] (g : ℕ) :
    ObjectProperty (SchemeOverField k) :=
  fun X ↦
    ∃ (_ : Curve X) (_ : Smooth X.hom) (_ : IsProper X.hom),
      Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = g

/-- Membership in `smoothProperOfGenus k g` is equivalent to the curve, smoothness,
properness, bijective global sections, and degree-one cohomology dimension conditions. -/
theorem smoothProperOfGenus_iff {k : Type u} [Field k] (g : ℕ)
    (X : SchemeOverField k) :
    smoothProperOfGenus k g X ↔
      ∃ (_ : Curve X) (_ : Smooth X.hom) (_ : IsProper X.hom),
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
          Scheme.Hom.cohomologyFinrank X.hom
            (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 = g := sorry

/-- The full subcategory of smooth proper curves of genus `g` over `k` whose global
functions are exactly `k`. -/
abbrev SmoothProperOfGenus (k : Type u) [Field k] (g : ℕ) :=
  (smoothProperOfGenus k g).FullSubcategory

/-- Over a finite field, smooth proper curves of a fixed genus greater than one have
finitely many isomorphism classes over that field. -/
theorem finiteSkeletonOfGenus {k : Type u} [Field k] [Finite k] (g : ℕ)
    (hg : 1 < g) :
    Finite (Skeleton (SmoothProperOfGenus k g)) := sorry

/-- The skeleton of smooth proper curves of genus `g` over a finite field is finite
when the genus bound `1 < g` is available as a fact. -/
instance instFiniteSkeletonOfGenus {k : Type u} [Field k] [Finite k] (g : ℕ)
    [Fact (1 < g)] : Finite (Skeleton (SmoothProperOfGenus k g)) := sorry

end AlgebraicGeometry.Curve
