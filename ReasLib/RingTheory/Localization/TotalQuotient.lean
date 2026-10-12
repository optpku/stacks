/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Ideal.MinimalPrime.ReducedDiagonal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps of Total Quotient Rings

This module provides the total quotient ring of a commutative ring and the map induced by a
ring homomorphism that preserves nonzerodivisors.
-/

universe u v

open scoped nonZeroDivisors

namespace Localization

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]

/-- The total quotient ring of a commutative ring, obtained by inverting all nonzerodivisors. -/
abbrev totalQuotientRing (R : Type u) [CommRing R] : Type u :=
  Localization (nonZeroDivisors R)

/-- A ring homomorphism preserving nonzerodivisors induces a map between total quotient rings.
The preservation witness is supplied explicitly. -/
noncomputable def totalQuotientMap
    (f : R →+* S)
    (h : nonZeroDivisors R ≤ Submonoid.comap f (nonZeroDivisors S)) :
    totalQuotientRing R →+* totalQuotientRing S :=
  IsLocalization.map (totalQuotientRing S) f h

/-- Compute the total-quotient-ring map on an element of the source ring. -/
theorem totalQuotientMap_apply
    (f : R →+* S)
    (h : nonZeroDivisors R ≤ Submonoid.comap f (nonZeroDivisors S))
    (x : R) :
    totalQuotientMap f h (algebraMap R (totalQuotientRing R) x) =
      algebraMap S (totalQuotientRing S) (f x) := sorry

/-- A flat algebra map preserves nonzerodivisors. -/
theorem algebraMap_nonZeroDivisors_le_comap_of_flat
    [Algebra R S] [Module.Flat R S] :
    nonZeroDivisors R ≤ Submonoid.comap (algebraMap R S) (nonZeroDivisors S) := sorry

end

section MinimalPrimes

variable (R : Type u) [CommRing R]

/-- The canonical map from the total quotient ring to the product of the
fraction rings of the minimal-prime quotients. -/
noncomputable def totalQuotientToFractionRingPi :
    totalQuotientRing R →+*
      ((q : minimalPrimes R) → FractionRing (R ⧸ q.1)) := by
  classical
  refine RingHom.pi fun q ↦ ?_
  let qQuot := R ⧸ q.1
  have hqMap :
      nonZeroDivisors R ≤
        Submonoid.comap (Ideal.Quotient.mk q.1) (nonZeroDivisors qQuot) := by
    intro x hx
    have hx_not_mem_q : x ∉ q.1 := by
      intro hxq
      exact Set.disjoint_left.mp
        (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes q.2) hxq hx
    change Ideal.Quotient.mk q.1 x ∈ nonZeroDivisors qQuot
    rw [mem_nonZeroDivisors_iff_ne_zero]
    exact fun hxq ↦ hx_not_mem_q (Ideal.Quotient.eq_zero_iff_mem.mp hxq)
  exact IsLocalization.map (FractionRing qQuot) (Ideal.Quotient.mk q.1) hqMap

/-- The minimal-prime total-quotient map sends a base-ring element to its
quotient class in every coordinate fraction ring. -/
theorem totalQuotientToFractionRingPi_apply (x : R) (q : minimalPrimes R) :
    totalQuotientToFractionRingPi R (algebraMap R (totalQuotientRing R) x) q =
      algebraMap (R ⧸ q.1) (FractionRing (R ⧸ q.1))
        (Ideal.Quotient.mk q.1 x) := by
  have hqMap :
      nonZeroDivisors R ≤
        Submonoid.comap (Ideal.Quotient.mk q.1)
          (nonZeroDivisors (R ⧸ q.1)) := by
    intro y hy
    change Ideal.Quotient.mk q.1 y ∈ nonZeroDivisors (R ⧸ q.1)
    rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hyq
    have : y ∈ q.1 := Ideal.Quotient.eq_zero_iff_mem.mp hyq
    exact Set.disjoint_left.mp
      (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes q.2) this hy
  change IsLocalization.map (FractionRing (R ⧸ q.1)) (Ideal.Quotient.mk q.1) hqMap
      (algebraMap R (totalQuotientRing R) x) = _
  exact IsLocalization.map_eq hqMap x

/-- For a reduced ring with finitely many minimal primes, the total quotient
ring is the product of the fraction rings of its minimal-prime quotients. -/
@[stacks 035P]
theorem totalQuotientToFractionRingPi_bijective [IsReduced R]
    (hfinite : (minimalPrimes R).Finite) :
    Function.Bijective (totalQuotientToFractionRingPi R) := by
  constructor
  · rw [RingHom.injective_iff_ker_eq_bot]
    apply le_antisymm
    · intro z hz
      rw [RingHom.mem_ker] at hz
      obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) z
      rw [Ideal.mem_bot]
      have hr : minimalPrimes.ReducedDiagonal.algHom
          (Ideal.Quotient.mk (nilradical R) r) = 0 := by
        funext q
        have hq := congr_fun hz q
        simp only [totalQuotientToFractionRingPi, RingHom.pi_apply,
          IsLocalization.map_mk'] at hq
        change IsLocalization.mk' (FractionRing (R ⧸ q.1))
            (Ideal.Quotient.mk q.1 r) _ = 0 at hq
        rw [IsLocalization.mk'_eq_zero_iff] at hq
        rcases hq with ⟨t, ht⟩
        have ht_ne : (t : R ⧸ q.1) ≠ 0 := nonZeroDivisors.ne_zero t.2
        rw [mul_eq_zero] at ht
        have hrq : Ideal.Quotient.mk q.1 r = 0 := ht.resolve_left ht_ne
        change Ideal.Quotient.mk q.1 r = 0
        exact hrq
      have hrnil : Ideal.Quotient.mk (nilradical R) r = 0 :=
        minimalPrimes.ReducedDiagonal.algHom_injective hr
      have hr0 : r = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, nilradical_eq_zero] at hrnil
        simpa using hrnil
      simp [hr0]
    · exact bot_le
  · classical
    -- Local instance justification (proof-local temporary data): enumerate the finite minimal-prime set to form the separating finite sums and products.
    letI : Fintype (minimalPrimes R) := hfinite.fintype
    intro y
    choose as has using fun q : minimalPrimes R ↦
      IsLocalization.surj (nonZeroDivisors (R ⧸ q.1)) (y q)
    let a : (q : minimalPrimes R) → R ⧸ q.1 := fun q ↦ (as q).1
    let s : (q : minimalPrimes R) → nonZeroDivisors (R ⧸ q.1) := fun q ↦ (as q).2
    have hs (q : minimalPrimes R) :
        y q * algebraMap (R ⧸ q.1) (FractionRing (R ⧸ q.1)) (s q) =
          algebraMap (R ⧸ q.1) (FractionRing (R ⧸ q.1)) (a q) := has q
    choose r hr using fun q : minimalPrimes R ↦
      Ideal.Quotient.mk_surjective (a q)
    choose d hd using fun q : minimalPrimes R ↦
      Ideal.Quotient.mk_surjective (s q).1
    have hd_not_mem (q : minimalPrimes R) : d q ∉ q.1 := by
      intro hdq
      have : (s q : R ⧸ q.1) = 0 := by
        rw [← hd q]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hdq
      exact nonZeroDivisors.ne_zero (s q).2 this
    have hchoose (q p : minimalPrimes R) (hpq : p ≠ q) :
        ∃ c : R, c ∈ p.1 ∧ c ∉ q.1 := by
      have hnle : ¬ p.1 ≤ q.1 := by
        intro hpq_le
        apply hpq
        exact Subtype.ext (hpq_le.antisymm (q.2.2 p.2.1 hpq_le))
      simpa only [SetLike.not_le_iff_exists] using hnle
    have hchoose' : ∀ q : minimalPrimes R,
        ∀ p : {p : minimalPrimes R // p ≠ q},
          ∃ c : R, c ∈ p.1.1 ∧ c ∉ q.1 :=
      fun q p ↦ hchoose q p.1 p.2
    choose c hc_mem hc_not using hchoose'
    let t : minimalPrimes R → R := fun q ↦
      ∏ p : {p : minimalPrimes R // p ≠ q}, c q p
    have ht_not_mem (q : minimalPrimes R) : t q ∉ q.1 := by
      dsimp only [t]
      rw [q.2.isPrime.prod_mem_iff]
      push Not
      intro p hp
      exact hc_not q p
    have ht_mem (q p : minimalPrimes R) (hqp : q ≠ p) : t q ∈ p.1 := by
      dsimp only [t]
      exact Ideal.prod_mem p.1 (Finset.mem_univ ⟨p, hqp.symm⟩)
        (hc_mem q ⟨p, hqp.symm⟩)
    let n : R := ∑ q : minimalPrimes R, t q * r q
    let d₀ : R := ∑ q : minimalPrimes R, t q * d q
    have hmk_n (q : minimalPrimes R) :
        Ideal.Quotient.mk q.1 n = Ideal.Quotient.mk q.1 (t q * r q) := by
      dsimp only [n]
      rw [map_sum, Finset.sum_eq_single q]
      · intro p hp hpq
        rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (ht_mem p q hpq), zero_mul]
      · simp
    have hmk_d (q : minimalPrimes R) :
        Ideal.Quotient.mk q.1 d₀ = Ideal.Quotient.mk q.1 (t q * d q) := by
      dsimp only [d₀]
      rw [map_sum, Finset.sum_eq_single q]
      · intro p hp hpq
        rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (ht_mem p q hpq), zero_mul]
      · simp
    have hd₀_mem : d₀ ∈ nonZeroDivisors R := by
      rw [mem_nonZeroDivisors_iff_right]
      intro z hzd
      have hzdiag : minimalPrimes.ReducedDiagonal.algHom
          (Ideal.Quotient.mk (nilradical R) z) = 0 := by
        funext q
        change Ideal.Quotient.mk q.1 z = 0
        have hmul : Ideal.Quotient.mk q.1 z * Ideal.Quotient.mk q.1 d₀ = 0 := by
          rw [← map_mul, hzd, map_zero]
        have hdq_ne : Ideal.Quotient.mk q.1 d₀ ≠ 0 := by
          rw [hmk_d q, map_mul, mul_ne_zero_iff]
          exact ⟨Ideal.Quotient.eq_zero_iff_mem.not.mpr (ht_not_mem q),
            Ideal.Quotient.eq_zero_iff_mem.not.mpr (hd_not_mem q)⟩
        exact (mul_eq_zero.mp hmul).resolve_right hdq_ne
      have hznil : Ideal.Quotient.mk (nilradical R) z = 0 :=
        minimalPrimes.ReducedDiagonal.algHom_injective hzdiag
      rw [Ideal.Quotient.eq_zero_iff_mem, nilradical_eq_zero] at hznil
      simpa using hznil
    refine ⟨IsLocalization.mk' (totalQuotientRing R) n ⟨d₀, hd₀_mem⟩, ?_⟩
    funext q
    simp only [totalQuotientToFractionRingPi, RingHom.pi_apply,
      IsLocalization.map_mk']
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    change algebraMap (R ⧸ q.1) (FractionRing (R ⧸ q.1))
        (Ideal.Quotient.mk q.1 n) =
      y q * algebraMap (R ⧸ q.1) (FractionRing (R ⧸ q.1))
        (Ideal.Quotient.mk q.1 d₀)
    rw [hmk_n q, hmk_d q, map_mul, map_mul, map_mul, map_mul,
      hr q, hd q, ← hs q]
    ring

end MinimalPrimes

section FractionRing

variable (R : Type u) [CommRing R]

/-- If `M` consists of nonzerodivisors, the total quotient rings of `R` and
`Localization M` are canonically equivalent as `R`-algebras. -/
@[stacks 02LW "(1)"]
noncomputable def fractionRingAlgEquiv (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R) :
    FractionRing R ≃ₐ[R] FractionRing (Localization M) :=
  -- Local declaration justification (defeq pin): this selects the intermediate
  -- localization action without registering a global algebra instance and creating diamonds.
  let f := mapToFractionRing (FractionRing R) M (Localization M) hM
  -- Local instance justification (defeq pin): select the localization algebra induced by `f`.
  letI : Algebra (Localization M) (FractionRing R) := RingHom.toAlgebra f.toRingHom
  -- Local instance justification (defeq pin): use the scalar tower induced by the selected algebra.
  letI : IsScalarTower R (Localization M) (FractionRing R) :=
    .of_algebraMap_eq fun r ↦ (f.commutes r).symm
  -- Local instance justification (defeq pin): use the corresponding fraction-ring structure.
  letI : IsFractionRing (Localization M) (FractionRing R) :=
    IsFractionRing.isFractionRing_of_isLocalization M (Localization M) (FractionRing R) hM
  (FractionRing.algEquiv (Localization M) (FractionRing R)).symm.restrictScalars R

/-- The total-quotient equivalence commutes with the canonical map from the
base ring. -/
@[simp, stacks 02LW "total-quotient localization equivalence on the base ring"]
theorem fractionRingAlgEquiv_algebraMap (M : Submonoid R)
    (hM : M ≤ nonZeroDivisors R) (r : R) :
    fractionRingAlgEquiv R M hM (algebraMap R (FractionRing R) r) =
      algebraMap R (FractionRing (Localization M)) r :=
  AlgEquiv.commutes (fractionRingAlgEquiv R M hM) r

end FractionRing

end Localization

namespace FractionRing

/-- The total quotient ring of a ring is canonically equivalent to the total
quotient ring of its total quotient ring. -/
@[stacks 02LW "(2)"]
noncomputable def iteratedAlgEquiv (R : Type u) [CommRing R] :
    FractionRing R ≃ₐ[R] FractionRing (FractionRing R) :=
  Localization.fractionRingAlgEquiv R (nonZeroDivisors R) le_rfl

end FractionRing
