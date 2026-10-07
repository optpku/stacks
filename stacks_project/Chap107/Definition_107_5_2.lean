module

public import stacks_project.Chap107.Remark_107_5_3_RelativeDimension
import StacksCheckRecall

@[expose] public section

/- Definition 107.5.2: if `f : T.toGroupoids ⟶ X` is a locally of finite type
morphism from an algebraic space to an algebraic stack, and `t ∈ |T|` is a
point with image `x ∈ |X|`, the relative dimension `dim_t(T_x)` is
`fiberDimensionAt f t`. Choose a morphism `Spec k ⟶ X` representing `x` and
a point `t'` of `T ×_X Spec k` mapping to `t`; then
`dim_t(T_x) = dim_{t'}(T ×_X Spec k)`. Such a `t'` exists by
Properties of Stacks, Lemma 100.4.3. -/
@[stacks 0DRG] #check AlgebraicGeometry.AlgebraicStack.fiberDimensionAt

#check AlgebraicGeometry.AlgebraicStack.fiberDimensionAt_eq
#check AlgebraicGeometry.AlgebraicStack.exists_relativeDimensionChoice
#check AlgebraicGeometry.AlgebraicStack.RelativeDimensionChoice.dimension
