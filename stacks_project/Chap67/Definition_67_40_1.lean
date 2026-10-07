module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_40_1_Proper
import StacksCheckRecall

@[expose] public section

/- Definition 67.40.1: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is proper if it is separated, finite type, and universally closed. -/
@[stacks 03ZM] #check AlgebraicGeometry.AlgebraicSpace.Proper
