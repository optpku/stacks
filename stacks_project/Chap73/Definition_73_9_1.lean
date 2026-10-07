module

public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 73.9.1: Let `S` be a scheme, and let `X` be an algebraic space over
`S`. An fpqc covering of `X` is a family of morphisms `{f_i : X_i ⟶ X}_{i ∈ I}`
of algebraic spaces such that each `f_i` is flat and such that for every affine
scheme `Z` and morphism `h : Z ⟶ X` there exists a standard fpqc covering
`{g_j : Z_j ⟶ Z}` which refines the family `{X_i ×_X Z ⟶ Z}_{i ∈ I}`. -/
@[stacks 03MQ] #check AlgebraicGeometry.AlgebraicSpace.FpqcCovering

#check AlgebraicGeometry.AlgebraicSpace.FpqcCovering.iff
