/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Algebraic.StronglyTranscendental
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Coefficient criteria for strong transcendence

Mathlib's `IsStronglyTranscendental` is the canonical predicate.  This leaf
exposes the coefficientwise form used in commutative-algebra arguments while
keeping the polynomial relation itself as the primitive statement.

@stack 00Q0
-/

open Polynomial

universe u v

namespace IsStronglyTranscendental

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Strong transcendence is equivalent to coefficientwise annihilation of
every polynomial relation. -/
@[stacks 00PZ "coefficientwise strong-transcendence criterion"]
theorem iff_mul_coeff_eq_zero {x : S} :
    IsStronglyTranscendental R x ↔
      ∀ (u : S) (p : R[X]),
        u * p.aeval x = 0 →
          ∀ n : ℕ, u * algebraMap R S (p.coeff n) = 0 := sorry
/- Proof strategy: apply `Polynomial.ext_iff` to the defining relation
`p.map (algebraMap R S) * C u = 0`, then use `coeff_mul_C` and `coeff_map`. -/

/-- A strongly transcendental element sends every annihilated polynomial
relation to coefficientwise annihilation. -/
@[stacks 00PZ "coefficientwise strong-transcendence readout"]
theorem mul_coeff_eq_zero {x : S} (hx : IsStronglyTranscendental R x)
    {u : S} {p : R[X]} (h : u * p.aeval x = 0) (n : ℕ) :
    u * algebraMap R S (p.coeff n) = 0 := sorry
/- Proof strategy: use the forward direction of `iff_mul_coeff_eq_zero`. -/

/-- Coefficientwise annihilation of all polynomial relations implies strong
transcendence. -/
@[stacks 00PZ "coefficientwise strong-transcendence constructor"]
theorem of_mul_coeff_eq_zero {x : S}
    (h : ∀ (u : S) (p : R[X]),
      u * p.aeval x = 0 → ∀ n : ℕ, u * algebraMap R S (p.coeff n) = 0) :
    IsStronglyTranscendental R x := sorry
/- Proof strategy: reconstruct the defining polynomial equality with
`Polynomial.ext` and the coefficient formula for `p.map _ * C u`. -/

/-- Lemma 10.123.8: strong transcendence descends simultaneously to a minimal-prime quotient of
the target and the induced quotient of the base. -/
@[stacks 00Q0]
theorem quotient_over_under_of_mem_minimalPrimes [IsReduced S]
    {x : S} (hx : IsStronglyTranscendental R x)
    (q : Ideal S) (hq : q ∈ minimalPrimes S) :
    IsStronglyTranscendental (R ⧸ q.under R) (Ideal.Quotient.mk q x) := sorry

end IsStronglyTranscendental
