module

public import stacks_project.Chap89.Definition_89_8_2_NormalizedBlowup
public import stacks_project.Chap89.Definition_89_8_2_Sequence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Definition 89.8.2: Let `S` be a scheme. Let `Y` be a 2-dimensional Noetherian integral
algebraic space over `S`. We say `Y` has a resolution of singularities by normalized blowups
if there exists a sequence `Y_n ⟶ ⋯ ⟶ Y_1 ⟶ Y_0 ⟶ Y` where each `Y_i` is proper over `Y`,
`Y_0 ⟶ Y` is the normalization, each `Y_i ⟶ Y_{i-1}` is a normalized blowup, and `Y_n` is
regular. -/
@[stacks 0BHX] #check AlgebraicGeometry.AlgebraicSpace.HasResolutionByNormalizedBlowups
#check AlgebraicGeometry.AlgebraicSpace.hasResolutionByNormalizedBlowups_iff
