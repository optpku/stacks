module

public import ReasLib.AlgebraicGeometry.Scheme.FinitePoints
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.33.4: there exists a non-affine scheme having three points. -/
@[stacks 028R] #check (AlgebraicGeometry.Scheme.exists_not_isAffine_card_eq_three :
  ∃ X : AlgebraicGeometry.Scheme.{u}, ¬ AlgebraicGeometry.IsAffine X ∧ Nat.card X = 3)
