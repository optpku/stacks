module

public import stacks_project.Chap100.Definition_100_11_8_ResidualGerbe
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (x : Points X)

/- Definition 100.11.8 (1): the residual gerbe of an algebraic stack `X` at a
point `x ∈ |X|` exists if the equivalent conditions of Lemma 100.11.7 hold. -/
@[stacks 06MU] #check HasResidualGerbe X x
#check HasResidualGerbe.iff_existsMonoSingletonAt
#check HasResidualGerbe.iff_existsReducedMonoSingletonAt
#check HasResidualGerbe.iff_existsMonoSurjectiveFlatSpecFieldAt

variable [HasResidualGerbe X x]

/- Definition 100.11.8 (2): if the residual gerbe of `X` at `x` exists, then it
is the strictly full subcategory `Z_x ⊂ X` constructed in Lemma 100.11.7. -/
@[stacks 06MU] #check residualGerbe X x
#check residualGerbeι X x
#check residualGerbe_spec

end AlgebraicGeometry.AlgebraicStack
