module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 101.8.1: an algebraic stack `X` is Noetherian if it is
quasi-compact, quasi-separated and locally Noetherian. -/
@[stacks 0510] #check (AlgebraicGeometry.AlgebraicStack.IsNoetherian :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X], Prop)
