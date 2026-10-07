module

public import Mathlib.AlgebraicGeometry.AffineScheme

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- There exists a non-affine scheme whose underlying carrier has exactly three points. -/
theorem exists_not_isAffine_card_eq_three :
    ∃ X : Scheme.{u}, ¬ IsAffine X ∧ Nat.card X = 3 :=
  sorry

end AlgebraicGeometry.Scheme
