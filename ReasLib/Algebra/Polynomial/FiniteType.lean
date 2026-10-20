module

public import ReasLib.Algebra.PolynomialSite
public import Mathlib.RingTheory.FiniteType

/-!
# Finite-type polynomial algebras

Finite-type polynomial algebras are precisely polynomial algebras on finitely many variables.
-/

@[expose] public section

universe u

namespace Algebra

/-- A polynomial `A`-algebra is of finite type if and only if it is isomorphic as an
`A`-algebra to `MvPolynomial (Fin n) A` for some `n`. -/
theorem IsPolynomial.finiteType_iff {A P : Type u} [CommRing A] [CommRing P] [Algebra A P] :
    (IsPolynomial A P ∧ FiniteType A P) ↔
      ∃ n : ℕ, Nonempty (P ≃ₐ[A] MvPolynomial (Fin n) A) :=
  sorry

end Algebra
