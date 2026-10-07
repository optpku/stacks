module

public import Mathlib.Algebra.Ring.NonZeroDivisors
public import ReasLib.RingTheory.Ideal.Maximal.Disjoint

/-!
# Prime Ideals and Nonzerodivisors

This leaf specializes the maximal-disjoint prime criterion to the canonical submonoid of
nonzerodivisors and records the resulting domain criterion. The source implication is accompanied
by its symmetric `iff` form for downstream use.

@stack 05KI
-/

@[expose] public section

open scoped nonZeroDivisors

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Lemma 10.28.12 (1): an ideal maximal among those disjoint from the nonzerodivisors is prime. -/
@[stacks 05KI "(1), maximal ideal avoiding nonzerodivisors"]
theorem isPrime_of_maximal_disjoint_nonZeroDivisors {I : Ideal R}
    (hI : Maximal
      (fun J : Ideal R => Disjoint (J : Set R) (R⁰ : Set R)) I) :
    I.IsPrime := sorry

end Ideal

namespace IsDomain

variable {R : Type u} [CommRing R] [Nontrivial R]

/-- Lemma 10.28.12 (2): if every nonzero prime ideal contains a nonzerodivisor, then the ring is a
domain. -/
@[stacks 05KI "(2), domain criterion"]
theorem of_prime_contains_nonZeroDivisor
    (hprime : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ →
      ∃ x : R, x ∈ P ∧ x ∈ R⁰) :
    IsDomain R := sorry

/-- A nontrivial commutative ring is a domain exactly when every nonzero prime ideal contains a
nonzerodivisor. -/
@[stacks 05KI "domain criterion iff"]
theorem iff_prime_contains_nonZeroDivisor :
    IsDomain R ↔
      ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ →
        ∃ x : R, x ∈ P ∧ x ∈ R⁰ := sorry

end IsDomain
