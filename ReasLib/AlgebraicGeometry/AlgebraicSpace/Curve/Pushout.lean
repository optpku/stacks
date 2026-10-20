module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Fibered.RestrictionComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing families of curves

Restriction along a pushout of schemes with a thickening and an affine map
is an equivalence on the fibre categories of families of curves.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Restriction of families of curves with cartesian squares as morphisms
along a pushout in `Over B` is an equivalence of fibre categories when
`i : T ⟶ T'` is a thickening and `f : T ⟶ S` is affine. -/
@[stacks 0D56]
instance restrictionComparison.instIsEquivalence {B : Scheme.{u}}
    {T T' S S' : Over B} {i : T ⟶ T'} {f : T ⟶ S} {inl : T' ⟶ S'} {inr : S ⟶ S'}
    [IsThickening i.left] [IsAffineHom f.left] (h : IsPushout i f inl inr) :
    (restrictionComparison (p B) h.w).IsEquivalence := sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
