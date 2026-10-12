/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_41_1_ValuativeCriterion
import StacksCheckRecall

@[expose]
public section

/- Definition 67.41.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
satisfies the uniqueness part of the valuative criterion if every solid valuative square
with `A` a valuation ring and `K` its field of fractions has at most one dotted lift
`Spec(A) ⟶ X`. -/
@[stacks 03IX] #check AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Uniqueness

/- Definition 67.41.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
satisfies the existence part of the valuative criterion if every solid valuative square
admits a field extension `K'/K`, a valuation ring `A' ⊂ K'` dominating `A`, and a morphism
`Spec(A') ⟶ X` making the extended diagram commute. -/
@[stacks 03IX] #check AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.Existence

/- Definition 67.41.1 (3): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
satisfies the valuative criterion if it satisfies both the uniqueness and existence parts. -/
@[stacks 03IX] #check AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion
