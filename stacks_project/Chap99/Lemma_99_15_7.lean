/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap98.Definition_98_5_1_Comparison
public import stacks_project.Chap99.Lemma_99_15_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 99.15.7

Restriction of the stack of curves along a thickening-plus-affine pushout
in `Over B` is an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.Spaces

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 99.15.7: if `i : T ⟶ T'` is a thickening and `f : T ⟶ S` is affine,
and `h` exhibits the square `T`, `T'`, `S`, `S'` as a pushout in `Over B`
(More on Morphisms, Lemma 37.14.3; `Over B` is `Sch_fppf`), then the functor
of fibre categories `restrictionComparison (p B) h.w`, i.e.
`Curves_{S'} ⥤ Curves_S ×_{Curves_T} Curves_{T'}`, is an equivalence. -/
@[stacks 0D56]
instance restrictionComparison.instIsEquivalence {B : Scheme.{u}}
    {T T' S S' : Over B} {i : T ⟶ T'} {f : T ⟶ S} {inl : T' ⟶ S'} {inr : S ⟶ S'}
    [IsThickening i.left] [IsAffineHom f.left] (h : IsPushout i f inl inr) :
    (restrictionComparison (p B) h.w).IsEquivalence := sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
