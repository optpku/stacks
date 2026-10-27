/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.PowerImage

/-!
# Shift-power generation

@stack 09EF

This leaf owns the generation predicate used for maps whose target elements satisfy a
shifted-polynomial relation.  Spectral, integral, and residue-field consequences belong
to separate theorem leaves; consumers that only need the hypothesis can import this file.
-/

@[expose] public section

universe u v

namespace RingHom

open Polynomial

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace ShiftPower

/-- The subset of `S` whose translate has a positive power coming from `R[X]`. -/
def generators (f : R →+* S) : Set S :=
  {x : S |
    ∃ n : ℕ, 0 < n ∧ ∃ P : R[X], Polynomial.map f P = (Polynomial.X - Polynomial.C x) ^ n}

/-- Membership in the shift-power generating set, in witness form. -/
theorem mem_generators_iff (f : R →+* S) {x : S} :
    x ∈ generators f ↔
      ∃ n : ℕ, 0 < n ∧ ∃ P : R[X], Polynomial.map f P =
        (Polynomial.X - Polynomial.C x) ^ n := Iff.rfl

/-- A ring homomorphism is shift-power generated when its source image together with these
translated-polynomial elements generate the target ring. This instance-free formulation is the
primary API for arbitrary ring homomorphisms. -/
@[stacks 09EF]
abbrev IsGenerated (f : R →+* S) : Prop :=
  RingHom.IsGeneratedBy f (generators f)

/-- The shift-power predicate is equivalent to top generation by its canonical adjoin. -/
theorem isGenerated_iff_adjoin_top (f : R →+* S) :
    IsGenerated f ↔ f.adjoin (generators f) = ⊤ := by
  letI : Algebra R S := f.toAlgebra
  change Subring.closure ((f.range : Set S) ∪ generators f) = ⊤ ↔
    Algebra.adjoin R (generators f) = ⊤
  rw [← Algebra.toSubring_eq_top, Algebra.adjoin_eq_ring_closure]
  rfl

namespace Witness

/-- A shift-power witness puts the corresponding power of its root in the homomorphism image. -/
lemma pow_mem_range
    (f : R →+* S) {x : S} {n : ℕ} {P : R[X]}
    (hP : Polynomial.map f P = (X - C x) ^ n) :
    x ^ n ∈ f.range := by
  have hzero : (-x) ^ n ∈ f.range := by
    show (-x) ^ n ∈ f.range
    have hcoeff : Polynomial.constantCoeff (P.map f) = (-x) ^ n := by
      rw [hP, map_pow, map_sub]
      simp
    exact ⟨P.coeff 0, by simpa only [constantCoeff_apply, coeff_map] using hcoeff⟩
  have hsign : (-1 : S) ^ n ∈ f.range :=
    f.range.pow_mem (f.range.neg_mem f.range.one_mem) n
  simpa only [← mul_pow, neg_one_mul, neg_neg] using f.range.mul_mem hsign hzero

/-- The next-to-leading coefficient of a shift-power witness puts the corresponding natural-number
multiple of its root in the homomorphism image. -/
lemma nsmul_mem_range
    (f : R →+* S) {x : S} {n : ℕ} (hn : 0 < n) {P : R[X]}
    (hP : Polynomial.map f P = (X - C x) ^ n) :
    n • x ∈ f.range := by
  have hcoeff : ((X - C x) ^ n).coeff (n - 1) = -(n • x) := by
    simpa using multiset_prod_X_sub_C_coeff_card_pred (Multiset.replicate n x)
      (by simpa using hn)
  apply f.range.neg_mem_iff.mp
  exact ⟨P.coeff (n - 1), by
    simpa only [coeff_map, hcoeff] using
      congrArg (fun Q : S[X] => Q.coeff (n - 1)) hP⟩

/-- In a field homomorphism, a nonzero natural-number multiple in the image can be divided out. -/
lemma mem_range_of_nsmul
    {K : Type*} {L : Type*} [Field K] [CommRing L] (φ : K →+* L)
    {n : ℕ} {x : L} (hn : (n : K) ≠ 0) (hx : n • x ∈ φ.range) :
    x ∈ φ.range := by
  obtain ⟨a, ha⟩ := hx
  have hcancel : φ ((n : K)⁻¹) * (n : L) = 1 := by
    rw [← map_natCast φ n, ← map_mul, inv_mul_cancel₀ hn, map_one]
  refine ⟨(n : K)⁻¹ * a, ?_⟩
  change φ ((n : K)⁻¹ * a) = x
  calc
    φ ((n : K)⁻¹ * a) = φ ((n : K)⁻¹) * (n • x) := by rw [map_mul, ha]
    _ = x := by rw [nsmul_eq_mul, ← mul_assoc, hcancel, one_mul]

/-- Over characteristic zero, a shift-power witness already puts its root in the base-field image. -/
lemma mem_range_charZero
    {K : Type*} {L : Type*} [Field K] [CommRing L] [CharZero K]
    (φ : K →+* L) {y : L} {n : ℕ} (hn : 0 < n) {P : K[X]}
    (hP : Polynomial.map φ P = (X - C y) ^ n) :
    y ∈ φ.range := by
  exact mem_range_of_nsmul φ (Nat.cast_ne_zero.mpr hn.ne') (nsmul_mem_range φ hn hP)

/-- In characteristic `p`, Frobenius expansion transports a shifted power to a shifted power of
the Frobenius image of its root. -/
lemma expand_frobenius_charP
    {K : Type*} {L : Type*} [Field K] [CommRing L] [Nontrivial L] (φ : K →+* L)
    {p : ℕ} [Fact p.Prime] [CharP K p] (y : L) (k m : ℕ) :
    Polynomial.expand L (p ^ k) ((X - C (y ^ (p ^ k))) ^ m) = (X - C y) ^ (p ^ k * m) := by
  letI : CharP L p := charP_of_injective_ringHom φ.injective p
  simp only [map_pow, map_sub, expand_X, expand_C]
  rw [pow_mul, sub_pow_expChar_pow]

/-- Contracting a characteristic-`p` shift-power witness produces a witness for the Frobenius image
of its root with the reduced exponent. -/
lemma contract_charP
    {K : Type*} {L : Type*} [Field K] [CommRing L] [Nontrivial L] (φ : K →+* L)
    {p : ℕ} [Fact p.Prime] [CharP K p] {y : L} {P : K[X]} (k m : ℕ)
    (hP : Polynomial.map φ P = (X - C y) ^ (p ^ k * m)) :
    Polynomial.map φ (Polynomial.contract (p ^ k) P) = (X - C (y ^ (p ^ k))) ^ m := by
  have hp : p ^ k ≠ 0 := pow_ne_zero k (Fact.out : p.Prime).ne_zero
  rw [map_contract hp, hP, ← expand_frobenius_charP φ y k m,
    Polynomial.contract_expand (p ^ k) hp]

/-- In characteristic `p`, a shift-power witness gives a prime-power image witness for its root. -/
lemma exists_prime_power_mem_range_charP
    {K : Type*} {L : Type*} [Field K] [CommRing L] [Nontrivial L] (φ : K →+* L)
    {p : ℕ} [Fact p.Prime] [CharP K p] {y : L} {n : ℕ} (hn : 0 < n) {P : K[X]}
    (hP : Polynomial.map φ P = (X - C y) ^ n) :
    ∃ k : ℕ, y ^ (p ^ k) ∈ φ.range := by
  obtain ⟨k, m, hm, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p (Fact.out : p.Prime).ne_one
  have hmpos : 0 < m := Nat.pos_of_ne_zero fun hmzero => hm (hmzero ▸ dvd_zero p)
  refine ⟨k, mem_range_of_nsmul φ (n := m) ?_ ?_⟩
  · show (m : K) ≠ 0
    exact fun h => hm ((CharP.cast_eq_zero_iff K p m).mp h)
  · show m • y ^ (p ^ k) ∈ φ.range
    exact nsmul_mem_range φ hmpos (contract_charP φ k m (hnm ▸ hP))

end Witness

/-- Shift-power polynomial image generation forces a ring homomorphism to be integral. -/
@[stacks 09EF]
theorem isIntegral
    (f : R →+* S) (hgen : IsGenerated f) :
    f.IsIntegral := by
  letI : Algebra R S := f.toAlgebra
  have hgens : ∀ x ∈ (f.range : Set S) ∪ generators f, _root_.IsIntegral R x := by
    intro x hx
    obtain hx | hx := hx
    · show _root_.IsIntegral R x
      obtain ⟨r, rfl⟩ := hx
      exact isIntegral_algebraMap
    · show _root_.IsIntegral R x
      obtain ⟨n, hn, P, hP⟩ := hx
      obtain ⟨r, hr⟩ := Witness.pow_mem_range f hP
      apply IsIntegral.of_pow hn
      rw [← hr]
      exact isIntegral_algebraMap
  change Subring.closure ((f.range : Set S) ∪ generators f) = ⊤ at hgen
  intro x
  change _root_.IsIntegral R x
  have hx : x ∈ Subring.closure ((f.range : Set S) ∪ generators f) := by
    rw [hgen]
    trivial
  exact Subring.closure_induction hgens isIntegral_zero isIntegral_one
    (fun _ _ _ _ => IsIntegral.add) (fun _ _ => IsIntegral.neg)
    (fun _ _ _ _ => IsIntegral.mul) hx

end ShiftPower

end RingHom
