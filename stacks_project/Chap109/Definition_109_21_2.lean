module

public import stacks_project.Chap109.Definition_109_21_2_Semistable
public import stacks_project.Chap109.Definition_109_21_2_Spaces
import StacksCheckRecall

@[expose] public section

/- Definition 109.21.2: a family of curves `f : X ⟶ S` is a semistable family
of curves if it is prestable and, for every point `s` of `S`, the fibre `X_s`
has genus at least `1` and has no rational tail. -/
@[stacks 0E6Z] #check AlgebraicGeometry.AlgebraicSpace.Semistable
