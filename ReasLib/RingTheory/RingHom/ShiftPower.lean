/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
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
        (Polynomial.X - Polynomial.C x) ^ n := sorry

/-- A ring homomorphism is shift-power generated when its source image together with these
translated-polynomial elements generate the target ring. This instance-free formulation is the
primary API for arbitrary ring homomorphisms. -/
@[stacks 09EF]
abbrev IsGenerated (f : R →+* S) : Prop :=
  RingHom.IsGeneratedBy f (generators f)

/-- The shift-power predicate is equivalent to top generation by its canonical adjoin. -/
theorem isGenerated_iff_adjoin_top (f : R →+* S) :
    IsGenerated f ↔ f.adjoin (generators f) = ⊤ := sorry

namespace Witness

/-- A shift-power witness puts the corresponding power of its root in the homomorphism image. -/
lemma pow_mem_range
    (f : R →+* S) {x : S} {n : ℕ} {P : R[X]}
    (hP : Polynomial.map f P = (X - C x) ^ n) :
    x ^ n ∈ f.range := sorry

/-- The next-to-leading coefficient of a shift-power witness puts the corresponding natural-number
multiple of its root in the homomorphism image. -/
lemma nsmul_mem_range
    (f : R →+* S) {x : S} {n : ℕ} (hn : 0 < n) {P : R[X]}
    (hP : Polynomial.map f P = (X - C x) ^ n) :
    n • x ∈ f.range := sorry

/-- In a field homomorphism, a nonzero natural-number multiple in the image can be divided out. -/
lemma mem_range_of_nsmul
    {K : Type*} {L : Type*} [Field K] [CommRing L] (φ : K →+* L)
    {n : ℕ} {x : L} (hn : (n : K) ≠ 0) (hx : n • x ∈ φ.range) :
    x ∈ φ.range := sorry

/-- Over characteristic zero, a shift-power witness already puts its root in the base-field image. -/
lemma mem_range_charZero
    {K : Type*} {L : Type*} [Field K] [CommRing L] [CharZero K]
    (φ : K →+* L) {y : L} {n : ℕ} (hn : 0 < n) {P : K[X]}
    (hP : Polynomial.map φ P = (X - C y) ^ n) :
    y ∈ φ.range := sorry

/-- In characteristic `p`, Frobenius expansion transports a shifted power to a shifted power of
the Frobenius image of its root. -/
lemma expand_frobenius_charP
    {K : Type*} {L : Type*} [Field K] [CommRing L] [Nontrivial L] (φ : K →+* L)
    {p : ℕ} [Fact p.Prime] [CharP K p] (y : L) (k m : ℕ) :
    Polynomial.expand L (p ^ k) ((X - C (y ^ (p ^ k))) ^ m) = (X - C y) ^ (p ^ k * m) := sorry

/-- Contracting a characteristic-`p` shift-power witness produces a witness for the Frobenius image
of its root with the reduced exponent. -/
lemma contract_charP
    {K : Type*} {L : Type*} [Field K] [CommRing L] [Nontrivial L] (φ : K →+* L)
    {p : ℕ} [Fact p.Prime] [CharP K p] {y : L} {P : K[X]} (k m : ℕ)
    (hP : Polynomial.map φ P = (X - C y) ^ (p ^ k * m)) :
    Polynomial.map φ (Polynomial.contract (p ^ k) P) = (X - C (y ^ (p ^ k))) ^ m := sorry

/-- In characteristic `p`, a shift-power witness gives a prime-power image witness for its root. -/
lemma exists_prime_power_mem_range_charP
    {K : Type*} {L : Type*} [Field K] [CommRing L] [Nontrivial L] (φ : K →+* L)
    {p : ℕ} [Fact p.Prime] [CharP K p] {y : L} {n : ℕ} (hn : 0 < n) {P : K[X]}
    (hP : Polynomial.map φ P = (X - C y) ^ n) :
    ∃ k : ℕ, y ^ (p ^ k) ∈ φ.range := sorry

end Witness

/-- Shift-power polynomial image generation forces a ring homomorphism to be integral. -/
@[stacks 09EF]
theorem isIntegral
    (f : R →+* S) (hgen : IsGenerated f) :
    f.IsIntegral := sorry

end ShiftPower

end RingHom
