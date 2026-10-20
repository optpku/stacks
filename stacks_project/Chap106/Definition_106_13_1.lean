module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.WellNighAffine
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 106.13.1: an algebraic stack `X` is well-nigh affine if there
exists an affine scheme `U` and a morphism `U ⟶ X` that is surjective, flat,
finite, and finitely presented. -/
@[stacks 0DUL] #check (AlgebraicGeometry.AlgebraicStack.IsWellNighAffine :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.GroupoidsOver S)
    [AlgebraicGeometry.AlgebraicStack X], Prop)
