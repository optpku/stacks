module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
import StacksCheckRecall

@[expose] public section

/- Definition 67.33.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
has relative dimension ≤ `d` if it has relative dimension ≤ `d` at every point of `|X|`. -/
@[stacks 06LR] #check AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE
#check AlgebraicGeometry.AlgebraicSpace.relativeDimensionLE_iff

/- Definition 67.33.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
has relative dimension `d` if it has relative dimension `d` at every point of `|X|`. -/
@[stacks 06LR] #check AlgebraicGeometry.AlgebraicSpace.RelativeDimension
#check AlgebraicGeometry.AlgebraicSpace.relativeDimension_iff
