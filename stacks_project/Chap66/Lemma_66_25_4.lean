module

public import stacks_project.Chap66.Lemma_66_25_4_Regular
public import stacks_project.Chap66.Lemma_66_25_4_Normal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 66.25.4: a regular algebraic space is normal. -/
@[stacks 0BGT] #check AlgebraicGeometry.AlgebraicSpace.IsRegular.instIsNormal
