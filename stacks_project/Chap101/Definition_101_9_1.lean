module

public import stacks_project.Chap101.Definition_101_9_1_Affine
import StacksCheckRecall

@[expose] public section

/- Definition 101.9.1: a morphism `f : X ⟶ Y` of algebraic stacks is affine
if it is representable by algebraic spaces and affine in the sense of
Section 100.3, i.e. `has (@AlgebraicSpace.Affine S) f`. -/
@[stacks 0CHQ] #check AlgebraicGeometry.Groupoids.Hom.Affine
