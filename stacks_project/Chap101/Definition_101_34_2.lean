module

public import stacks_project.Chap101.Definition_101_34_2_Presentation
public import stacks_project.Chap101.Definition_101_34_2_EtaleSmoothLocal
import StacksCheckRecall

@[expose] public section

/- Definition 101.34.2: let `P` be a property of morphisms of algebraic spaces
which is étale-smooth local on the source-and-target. We say a DM morphism
`f : X ⟶ Y` of algebraic stacks has property `P` if the equivalent mixed
étale-smooth conditions of Lemma 101.34.1 hold. -/
@[stacks 0CIG] #check AlgebraicGeometry.AlgebraicStack.hasEtaleSmoothLocalAtSourceAndTarget
