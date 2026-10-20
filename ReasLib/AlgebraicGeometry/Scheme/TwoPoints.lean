module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme whose underlying topological space has exactly two points is affine. -/
theorem isAffine_of_natCard_eq_two {X : Scheme.{u}} (hX : Nat.card X = 2) :
    IsAffine X := sorry

end AlgebraicGeometry
