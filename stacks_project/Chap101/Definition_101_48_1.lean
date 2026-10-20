module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Decent
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 101.48.1: an algebraic stack `X` is decent if every point
`x ∈ |X|` satisfies the equivalent conditions of Lemma 100.14.1: some,
equivalently any, morphism `Spec(k) ⟶ X` in the class of `x` is
quasi-compact. -/
@[stacks 0GW1] #check (AlgebraicGeometry.AlgebraicStack.IsDecent :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X], Prop)
