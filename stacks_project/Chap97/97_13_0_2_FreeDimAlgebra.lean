module

public import ReasLib.RingTheory.Algebra.FreeDimensional

universe u

/- 97.13.0.2: The groupoid of distinguished finite free algebras over a ring. -/
#check
  (@AlgebraicGeometry.FreeDimAlgebra : ∀ (R : Type u) [CommRing R] (d : ℕ) [NeZero d], CategoryTheory.Grpd.{u, u})
