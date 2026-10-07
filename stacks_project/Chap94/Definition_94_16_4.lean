module

public import stacks_project.Chap94.Definition_94_16_4_Smooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- Definition 94.16.4: a groupoid `(U, R, s, t, c)` in algebraic spaces over an
algebraic space `B` over a scheme `S` is a smooth groupoid if `s, t : R ⟶ U`
are smooth morphisms of algebraic spaces. -/
@[stacks 04TH] #check AlgebraicGeometry.GroupoidAlgebraicSpace.Smooth
