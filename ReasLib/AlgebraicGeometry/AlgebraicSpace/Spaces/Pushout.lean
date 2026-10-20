module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Fibered.RestrictionComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing finite-presentation, flat, proper algebraic spaces

Restriction along a thickening-affine pushout of schemes is an equivalence
on the fibre categories of finite-presentation, flat, proper algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace FpFlatProperGroupoids

/-- Restriction of finite-presentation, flat, proper algebraic spaces with
cartesian squares as morphisms along a pushout in `Over B` is an equivalence
of fibre categories when `i : T ⟶ T'` is a thickening and `f : T ⟶ S` is affine. -/
@[stacks 0D1J]
instance restrictionComparison.instIsEquivalence {B : Scheme.{u}}
    {T T' S S' : Over B} {i : T ⟶ T'} {f : T ⟶ S} {inl : T' ⟶ S'} {inr : S ⟶ S'}
    [IsThickening i.left] [IsAffineHom f.left] (h : IsPushout i f inl inr) :
    (restrictionComparison (pFpFlatProperGroupoids B) h.w).IsEquivalence := sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
