module

public import stacks_project.Chap106.Definition_106_8_1_FormallySmooth
import StacksCheckRecall

@[expose] public section

/- Definition 106.8.1: a morphism `f : X ⟶ Y` of algebraic stacks is
formally smooth if it is formally smooth on objects as a 1-morphism of
categories fibred in groupoids, in the sense of Criteria for Representability,
Section 97.6. -/
@[stacks 0DNW] #check AlgebraicGeometry.AlgebraicStack.FormallySmooth
