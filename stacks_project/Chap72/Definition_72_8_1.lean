module

public import stacks_project.Chap72.Definition_72_8_1_Integral
public import stacks_project.Chap72.Definition_72_8_1_Modification
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 72.8.1: Let `S` be a scheme. Let `X` be an integral algebraic space
over `S`. A modification of `X` is a birational proper morphism `f : X' ⟶ X` of
algebraic spaces over `S` with `X'` integral. -/
@[stacks 0AD8] #check AlgebraicGeometry.AlgebraicSpace.IsModification
#check AlgebraicGeometry.AlgebraicSpace.isModification_iff
