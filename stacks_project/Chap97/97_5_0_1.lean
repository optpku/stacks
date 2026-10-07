module

public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap97.«97_5_0_1_Restrict»
import StacksCheckRecall

@[expose] public section

/- 97.5.0.1: the commuting square p(x_{i'}|_U) ⟶ (y_i|_{U_{i'}})|_U over
p(x) ⟶ y_i|_U, with right vertical the canonical identification of iterated
restriction. -/
@[stacks 06CU] #check AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.commSq
