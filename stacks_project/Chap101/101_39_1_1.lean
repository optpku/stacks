module

public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»
import StacksCheckRecall

@[expose] public section

/- 101.39.1.1: the solid 2-commutative valuative square
`Spec(K) —x→ X` over `Spec(A) —y→ Y` with vertical `j : Spec(K) ⟶ Spec(A)`,
where `A` is a valuation ring with fraction field `K`, as a morphism of algebraic
stacks. The 2-cell is `γ : j ≫ y ≅ x ≫ f`. The dashed fill-in is not part of
this square. -/
@[stacks 0CLB] #check AlgebraicGeometry.AlgebraicStack.ValuativeCommSq
