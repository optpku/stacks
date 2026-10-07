module

public import stacks_project.Chap100.Definition_100_4_2_Points
import StacksCheckRecall

@[expose] public section

/- Definition 100.4.2: a point of an algebraic stack `X` is an equivalence class of
morphisms from spectra of fields into `X`. The set of points of `X` is denoted `|X|`. -/
@[stacks 04XG] #check AlgebraicGeometry.AlgebraicStack.Points
