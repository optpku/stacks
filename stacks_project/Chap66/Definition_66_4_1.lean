module

public import stacks_project.Chap66.Definition_66_4_1_Points
import StacksCheckRecall

@[expose] public section

/- Definition 66.4.1: a point of an algebraic space `X` over a scheme `S` is an
equivalence class of morphisms from spectra of fields into `X`. The set of points
of `X` is denoted `|X|`. -/
@[stacks 03BU] #check AlgebraicGeometry.AlgebraicSpace.Points
