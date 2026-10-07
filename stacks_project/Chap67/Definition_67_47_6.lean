module

public import stacks_project.Chap67.Definition_67_47_6_Dominant
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 67.47.6: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`.
Assume `|X|` and `|Y|` are irreducible. A rational map from `X` to `Y` is called dominant if
any representative `f : U ⟶ Y` is a dominant morphism in the sense of Definition 67.18.1. -/
@[stacks 0EMS] #check AlgebraicGeometry.AlgebraicSpace.RationalMap.IsDominant
