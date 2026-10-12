/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Polynomial.Eval.Subring
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.SeparableDegree
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

namespace Polynomial.Frobenius

variable {R : Type*} [CommSemiring R] {p : ℕ} [ExpChar R p] {P : R[X]}

/-- Polynomials whose coefficients lie in the image of Frobenius. -/
noncomputable def range (R : Type*) [CommSemiring R] (p : ℕ) [ExpChar R p] : Subsemiring R[X] :=
  (Polynomial.mapRingHom (frobenius R p)).rangeS

/-- Membership in the polynomial Frobenius range is equivalent to every coefficient being a
`p`th power. -/
theorem mem_range_iff_coeff_eq_pow :
    P ∈ range R p ↔ ∀ n : ℕ, ∃ b : R, P.coeff n = b ^ p := sorry

end Polynomial.Frobenius

namespace Polynomial

/-- Frobenius-image membership descends across a coefficient ring equivalence. -/
theorem mem_frobenius_range_of_map_ringEquiv_symm
    {F₁ : Type*} {F₂ : Type*} [Field F₁] [Field F₂]
    {p : ℕ} [ExpChar F₁ p] [ExpChar F₂ p]
    (e : F₁ ≃+* F₂) {P : Polynomial F₂}
    (h : P.map e.symm.toRingHom ∈ Set.range (Polynomial.map (frobenius F₁ p))) :
    P ∈ Set.range (Polynomial.map (frobenius F₂ p)) := by
  rcases h with ⟨Q, hQ⟩
  refine ⟨Q.map e.toRingHom, ?_⟩
  apply Polynomial.map_injective (f := e.symm.toRingHom) e.symm.injective
  have hcomp :
      ((e.symm : F₂ →+* F₁).comp ((frobenius F₂ p).comp (e : F₁ →+* F₂))) =
        frobenius F₁ p := by
    ext x
    simp [RingHom.comp_apply, frobenius_def, map_pow]
  simpa [Polynomial.map_map, hcomp] using hQ

/-- Lemma 9.12.1 (Tag 09H0): an irreducible polynomial with zero derivative is an iterated
positive-characteristic `expand` of an irreducible separable polynomial. -/
theorem existsIrreducibleSeparableExpandOfDerivativeEqZero
    {F : Type*} [Field F] {P : F[X]} (hP : Irreducible P) (hderiv : P.derivative = 0) :
    0 < ringChar F ∧
      ∃ n : ℕ, ∃ Q : F[X],
        P = expand F ((ringChar F) ^ n) Q ∧ Irreducible Q ∧ Q.Separable := by
  have hchar_ne_zero : ringChar F ≠ 0 := by
    intro hchar
    -- Local instance justification (proof-local temporary data): identify the zero characteristic case in order to apply the derivative criterion.
    letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).1 hchar
    exact (separable_iff_derivative_ne_zero hP).1 hP.separable hderiv
  have hchar : 0 < ringChar F := Nat.pos_of_ne_zero hchar_ne_zero
  -- Local instance justification (proof-local temporary data): expose the nonzero characteristic as an instance for the separable-contraction construction.
  letI : NeZero (ringChar F) := ⟨hchar_ne_zero⟩
  -- Local instance justification (proof-local temporary data): the characteristic of a field is prime once it is positive, as required by the contraction API.
  letI : Fact (ringChar F).Prime := CharP.char_is_prime_of_pos F (ringChar F)
  have hcontraction := hP.hasSeparableContraction (ringChar F)
  obtain ⟨hQsep, n, hQP⟩ := hcontraction.isSeparableContraction
  have hQirr : Irreducible hcontraction.contraction :=
    of_irreducible_expand_pow (Nat.ne_of_gt hchar) (hQP ▸ hP)
  exact ⟨hchar, n, hcontraction.contraction, hQP.symm, hQirr, hQsep⟩

end Polynomial
