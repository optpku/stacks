module

public import stacks_project.Chap89.Definition_89_8_1_Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 89.8.1: Let `S` be a scheme. Let `Y` be a Noetherian integral algebraic space
over `S`. A resolution of singularities of `Y` is a modification `f : X ⟶ Y` such that
`X` is regular. -/
@[stacks 0BHW] #check AlgebraicGeometry.AlgebraicSpace.IsResolution
#check AlgebraicGeometry.AlgebraicSpace.isResolution_iff
