/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_37_1_Proper
public import stacks_project.Chap101.Lemma_101_39_8_Uniqueness
public import stacks_project.Chap101.Lemma_101_39_12_Existence

/-!
# Valuative criterion for properness

A finite-type quasi-separated morphism of algebraic stacks is proper if and
only if it satisfies both the uniqueness and existence parts of the valuative
criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Proper

/-- Lemma 101.43.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Assume
`f` is of finite type and quasi-separated. Then `f` is proper if and only if
`f` satisfies both the uniqueness and existence parts of the valuative
criterion. -/
@[stacks 0CLZ]
theorem iff_valuativeCriterion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] :
    Proper f ↔ ValuativeCriterion.Uniqueness f ∧ ValuativeCriterion.Existence f :=
  sorry

/-- A finite-type quasi-separated morphism of algebraic stacks that satisfies
both the uniqueness and existence parts of the valuative criterion is proper. -/
instance of_valuativeCriterion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f]
    [ValuativeCriterion.Uniqueness f] [ValuativeCriterion.Existence f] :
    Proper f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Proper
