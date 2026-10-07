module

public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
import StacksCheckRecall

@[expose] public section

/- Definition 101.17.1 (1): a morphism `f : X ⟶ Y` of algebraic stacks is
locally of finite type if the equivalent conditions of Lemma 101.16.1 hold
with `P` = locally of finite type. -/
@[stacks 06FS] #check AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/- Definition 101.17.1 (2): a morphism `f : X ⟶ Y` of algebraic stacks is
of finite type if it is locally of finite type and quasi-compact. -/
@[stacks 06FS] #check AlgebraicGeometry.AlgebraicStack.FiniteType
