/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Closed immersions of algebraic stacks and the valuative criterion

A closed immersion of algebraic stacks satisfies both the existence part and
the uniqueness part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.ValuativeCriterion

/-- Lemma 101.39.14 (1): A closed immersion of algebraic stacks satisfies the
existence part of the valuative criterion. -/
@[stacks 0CLP]
instance Existence.of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Existence f :=
  sorry

/-- Lemma 101.39.14 (2): A closed immersion of algebraic stacks satisfies the
uniqueness part of the valuative criterion. -/
@[stacks 0CLP]
instance Uniqueness.of_closedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [ClosedImmersion f] :
    Uniqueness f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ValuativeCriterion
