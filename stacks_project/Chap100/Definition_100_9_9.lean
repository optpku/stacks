module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 100.9.9 (1): an open substack of an algebraic stack `X` is a
strictly full subcategory `X' ⊂ X` such that `X'` is an algebraic stack and
`X' ⟶ X` is an open immersion. -/
@[stacks 04YM] #check (AlgebraicGeometry.AlgebraicStack.Substack.IsOpen :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    CategoryTheory.ObjectProperty X.total → Prop)

/- Definition 100.9.9 (2): a closed substack of an algebraic stack `X` is a
strictly full subcategory `X' ⊂ X` such that `X'` is an algebraic stack and
`X' ⟶ X` is a closed immersion. -/
@[stacks 04YM] #check (AlgebraicGeometry.AlgebraicStack.Substack.IsClosed :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    CategoryTheory.ObjectProperty X.total → Prop)

/- Definition 100.9.9 (3): a locally closed substack of an algebraic stack `X`
is a strictly full subcategory `X' ⊂ X` such that `X'` is an algebraic stack
and `X' ⟶ X` is an immersion. -/
@[stacks 04YM] #check (AlgebraicGeometry.AlgebraicStack.Substack.IsLocallyClosed :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S),
    CategoryTheory.ObjectProperty X.total → Prop)
