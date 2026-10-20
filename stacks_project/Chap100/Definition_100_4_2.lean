module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 100.4.2: a point of an algebraic stack `X` is an equivalence class of
morphisms from spectra of fields into `X`. The set of points of `X` is denoted `|X|`. -/
@[stacks 04XG] #check (AlgebraicGeometry.AlgebraicStack.Points :
  {S : AlgebraicGeometry.Scheme.{u}} → (X : AlgebraicGeometry.GroupoidsOver S) →
    [AlgebraicGeometry.AlgebraicStack X] → Type (u + 1))
