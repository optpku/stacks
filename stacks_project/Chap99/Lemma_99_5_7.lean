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
public import stacks_project.Chap99.Lemma_99_5_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 99.5.7

Restriction of `CohStack` along a thickening-plus-affine pushout in `Over S`
is an equivalence of fibre categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor Limits
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

/-- Lemma 99.5.7: in Situation 99.5.1, if `i : Z ⟶ Z'` is a thickening and
`g : Z ⟶ Y` is affine, and `h` exhibits the square `Z`, `Z'`, `Y`, `Y'` as a
pushout in `Over S` (More on Morphisms, Lemma 37.14.3), then the functor of
fibre categories `restrictionComparison (p f) h.w`, i.e.
`Coh_{X/B, Y'} ⥤ Coh_{X/B, Y} ×_{Coh_{X/B, Z}} Coh_{X/B, Z'}`, is an
equivalence. -/
@[stacks 08LQ]
instance restrictionComparison.instIsEquivalence {S : Scheme.{u}}
    {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    {Z Z' Y Y' : Over S} {i : Z ⟶ Z'} {g : Z ⟶ Y} {inl : Z' ⟶ Y'} {inr : Y ⟶ Y'}
    [IsThickening i.left] [IsAffineHom g.left] (h : IsPushout i g inl inr) :
    (restrictionComparison (p f) h.w).IsEquivalence := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
