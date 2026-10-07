module

public import Mathlib.RingTheory.NoetherNormalization

@[expose] public section

universe u v

namespace Algebra

/-- A nontrivial finite-type algebra over a field admits a finite injective
algebra homomorphism from a polynomial algebra in finitely many variables. -/
theorem exists_injective_finite_mvPolynomial
    (field : Type u) (ring : Type v) [Field field] [CommRing ring] [Nontrivial ring]
    [Algebra field ring] [Algebra.FiniteType field ring] :
    ∃ count : ℕ, ∃ embedding : MvPolynomial (Fin count) field →ₐ[field] ring,
      Function.Injective embedding ∧ embedding.Finite := sorry

end Algebra
