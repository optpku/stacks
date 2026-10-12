/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap76.Lemma_76_7_6_Comparison

/-!
# Base change of relative differentials of algebraic spaces

On a cartesian square of algebraic spaces, the canonical comparison from the
pullback of relative differentials to the relative differentials of the base
change is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Differentials

variable {S : Scheme.{u}}

/-- For a cartesian square of algebraic spaces, the canonical comparison from the
pullback of relative differentials to the relative differentials after base change is
an isomorphism. -/
instance comparison_isIso_of_isPullback
    {X X' Y Y' : AlgebraicSpace S} {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    (hpb : IsPullback g' f' f g) :
    IsIso (comparison g' g f f' hpb.w) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Differentials
