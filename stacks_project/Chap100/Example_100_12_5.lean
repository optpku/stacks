module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Example_100_12_5_Quotient

/-!
# Dimension of quotient stacks

The dimension of `[X / G]` for finite-type schemes over a field is
`dim X - dim G`. In particular `dim (BG) = -dim G` may be negative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {k : Type u} [Field k]

/-- Example 100.12.5 (1): if `X` is a scheme of finite type over a field `k` and
`G` is a group scheme of finite type over `k` acting on `X`, then
`dimension (quotient G X) = dimensionDiff (topologicalKrullDim X.X.left)
(topologicalKrullDim G.X.left)`. -/
@[stacks 0AFR]
theorem dimension_quotient (G : GroupScheme (Spec (.of k))) (X : GroupScheme.Action G)
    [Algebraic X.X] [Algebraic G.X] :
    dimension (quotient G X) =
      dimensionDiff (topologicalKrullDim X.X.left) (topologicalKrullDim G.X.left) :=
  sorry

/-- Example 100.12.5 (2): the classifying stack `BG = classifying G` has
`dimension (classifying G) = dimensionDiff 0 (topologicalKrullDim G.X.left)`. -/
@[stacks 0AFR]
theorem dimension_classifying (G : GroupScheme (Spec (.of k))) [Algebraic G.X] :
    dimension (classifying G) =
      dimensionDiff 0 (topologicalKrullDim G.X.left) :=
  sorry

/-- Example 100.12.5 (3): if `G` has positive dimension, then
`dimension (classifying G)` is a negative integer, in contrast to dimensions of
schemes or algebraic spaces. -/
@[stacks 0AFR]
theorem dimension_classifying_lt_zero (G : GroupScheme (Spec (.of k)))
    [Algebraic G.X] (hG : 0 < topologicalKrullDim G.X.left) :
    dimension (classifying G) < (0 : EInt) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
