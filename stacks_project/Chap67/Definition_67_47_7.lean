module

public import stacks_project.Chap67.Definition_67_47_7_Irreducible
public import stacks_project.Chap67.Definition_67_47_7_Birational
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable {S : Scheme.{u}} (X Y : AlgebraicSpace S)
variable [AlgebraicSpace.IsIrreducible X] [AlgebraicSpace.IsIrreducible Y]

/- Definition 67.47.7: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`
with `|X|` and `|Y|` irreducible. We say `X` and `Y` are birational if they are isomorphic
in the category of irreducible algebraic spaces over `S` and dominant rational maps. -/
@[stacks 0EMT] #check (AlgebraicGeometry.AlgebraicSpace.Birational X Y : Prop)

#check AlgebraicGeometry.AlgebraicSpace.PartialIso
