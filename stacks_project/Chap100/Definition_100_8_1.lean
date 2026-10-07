module

public import stacks_project.Chap100.Definition_100_8_1_Mono
import StacksCheckRecall

@[expose] public section

/- Definition 100.8.1: a morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if it is representable by algebraic spaces and a monomorphism
in the sense of Section 100.3. -/
@[stacks 04ZW] #check AlgebraicGeometry.Groupoids.Hom.Mono
