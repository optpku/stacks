module

public import stacks_project.Chap106.Definition_106_13_1_WellNighAffine
import StacksCheckRecall

@[expose] public section

/- Definition 106.13.1: an algebraic stack `X` is well-nigh affine if there
exists an affine scheme `U` and a morphism `U ⟶ X` that is surjective, flat,
finite, and finitely presented. -/
@[stacks 0DUL] #check AlgebraicGeometry.AlgebraicStack.IsWellNighAffine
