module

public import Mathlib.AlgebraicGeometry.Noetherian
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap107.Situation_107_2_1_Instances
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

section

variable {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
variable [AlgebraicStack X]
variable [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]

/- Situation 107.2.1 (1): `S` is a locally Noetherian scheme. -/
@[stacks 0DQU] #check (inferInstance : IsLocallyNoetherian S)

/- Situation 107.2.1 (2): `X` is an algebraic stack over `S`. -/
@[stacks 0DQU] #check (X : GroupoidsOver S)
@[stacks 0DQU] #check (inferInstance : AlgebraicStack X)

/- Situation 107.2.1 (3): `X` is locally of finite type over `S`. -/
@[stacks 0DQU] #check
  (inferInstance : AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X))

end
