/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap107.Lemma_107_5_9_RelativeDimension
import StacksCheckRecall

@[expose] public section

/- Definition 107.5.7: if `f : T ⟶ X` is a locally of finite type morphism
between locally Noetherian algebraic stacks, and `t ∈ |T|` is a point with
image `x ∈ |X|`, the relative dimension `dim_t(T_x)` is
`relativeDimensionAt f t`, equal to `dimensionAt t'` for a point `t'` of
`T ×_X Spec k` mapping to `t`. -/
@[stacks 0DRL] #check AlgebraicGeometry.AlgebraicStack.relativeDimensionAt

#check AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_eq
#check AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_spec
