module

public import Mathlib.Algebra.DualNumber
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

universe u v

namespace Algebra

/-- A nontrivial commutative algebra over an algebraically closed field with exactly two
subalgebras is algebra equivalent to the product of two copies of the field or its dual numbers. -/
theorem nonempty_algEquiv_prod_or_dualNumber_of_two_subalgebras
    {k : Type u} {A : Type v} [Field k] [IsAlgClosed k] [CommRing A] [Nontrivial A]
    [Algebra k A] (h_subalgebras : Nat.card (Subalgebra k A) = 2) :
    Nonempty (A ≃ₐ[k] (k × k)) ∨ Nonempty (A ≃ₐ[k] DualNumber k) := sorry

end Algebra
