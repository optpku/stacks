module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

universe u v

namespace Ideal.Quotient

/-- The quotient of a finite-type commutative algebra over a field by a maximal ideal
is finite-dimensional over the base field. -/
@[instance]
theorem finiteDimensional_of_finiteType
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] : FiniteDimensional k (A ⧸ m) := sorry

end Ideal.Quotient
