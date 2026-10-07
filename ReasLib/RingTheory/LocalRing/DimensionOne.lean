module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Ideal.MinimalPrime.Localization

@[expose] public section

/-!
# One-Dimensional Local Rings

This module packages the minimal-prime and total-fraction-ring API used for
one-dimensional Noetherian local rings.

@stack 00P9
-/

universe u

open IsLocalRing
open scoped nonZeroDivisors

namespace IsLocalRing.DimensionOne

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A one-dimensional Noetherian local ring is not Artinian. -/
@[stacks 00P9 "one-dimensional local rings are non-Artinian"]
theorem not_isArtinian_of_krullDim_eq_one
    (hdim : ringKrullDim R = 1) :
    ¬ IsArtinianRing R := sorry

/-- The self-module depth of a one-dimensional Noetherian local ring is at most one. -/
@[stacks 00P9 "depth bound in dimension one"]
theorem self_moduleDepth_le_one_of_krullDim_eq_one
    (hdim : ringKrullDim R = 1) :
    moduleDepth R R ≤ 1 := sorry

/-- In a Noetherian one-dimensional local ring, a member of the maximal ideal generates an
ideal with maximal radical exactly when it avoids all minimal primes. -/
@[stacks 0C3R]
theorem maximalIdeal_radical_span_singleton_iff_not_mem_minimalPrimes
    (hdim : ringKrullDim R = 1) {f : R} (hf_mem : f ∈ maximalIdeal R) :
    maximalIdeal R = (Ideal.span ({f} : Set R)).radical ↔
      ∀ p : minimalPrimes R, f ∉ p.1 := sorry

/-- The localization away from a maximal-ideal element in a Noetherian one-dimensional local
ring decomposes over minimal primes exactly when that element avoids all minimal primes. -/
theorem away_equiv_pi_minimalPrimeLocalizations_iff_not_mem_minimalPrimes
    (hdim : ringKrullDim R = 1) {f : R} (hf_mem : f ∈ maximalIdeal R) :
    Nonempty (Localization.Away f ≃ₐ[R] ((p : minimalPrimes R) → Localization.AtPrime p.1)) ↔
      ∀ p : minimalPrimes R, f ∉ p.1 := sorry

/-- A Noetherian one-dimensional local ring has a maximal-ideal element whose principal ideal
has maximal radical. -/
theorem exists_mem_maximalIdeal_radical_span_singleton
    (hdim : ringKrullDim R = 1) :
    ∃ f : R, f ∈ maximalIdeal R ∧
      maximalIdeal R = (Ideal.span ({f} : Set R)).radical := sorry

/-- In a Noetherian one-dimensional local ring of depth one, a maximal-ideal element is a
nonzerodivisor exactly when it avoids all minimal primes. -/
theorem mem_nonZeroDivisors_iff_not_mem_minimalPrimes_of_moduleDepth_eq_one
    (hdim : ringKrullDim R = 1) (hdepth : moduleDepth R R = 1)
    {f : R} (hf_mem : f ∈ maximalIdeal R) :
    f ∈ nonZeroDivisors R ↔ ∀ p : minimalPrimes R, f ∉ p.1 := sorry

/-- In a Noetherian one-dimensional local ring of depth one, localization away from a
maximal-ideal element is a total fraction ring exactly when that element is a nonzerodivisor. -/
theorem away_isFractionRing_iff_mem_nonZeroDivisors_of_moduleDepth_eq_one
    (hdim : ringKrullDim R = 1) (hdepth : moduleDepth R R = 1)
    {f : R} (hf_mem : f ∈ maximalIdeal R) :
    IsFractionRing R (Localization.Away f) ↔ f ∈ nonZeroDivisors R := sorry

/-- For a reduced Noetherian one-dimensional local ring, the products of the minimal-prime
localizations and residue fields give equivalent away-localization criteria. -/
theorem away_equiv_pi_minimalPrimeResidueFields_iff
    (hdim : ringKrullDim R = 1) [IsReduced R]
    {f : R} (hf_mem : f ∈ maximalIdeal R) :
    Nonempty (Localization.Away f ≃ₐ[R] ((p : minimalPrimes R) → p.1.ResidueField)) ↔
      Nonempty (Localization.Away f ≃ₐ[R] ((p : minimalPrimes R) → Localization.AtPrime p.1)) :=
  sorry

/-- A reduced Noetherian local ring of Krull dimension one has self-module depth one. -/
theorem self_moduleDepth_eq_one_of_isReduced
    (hdim : ringKrullDim R = 1) [IsReduced R] :
    moduleDepth R R = 1 := sorry

end

end IsLocalRing.DimensionOne

namespace IsLocalRing.PrincipalMaximalIdeal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private theorem exists_nat_ringKrullDim_eq_of_le {d : ℕ}
    (h : ringKrullDim R ≤ d) :
    ∃ n : ℕ, n ≤ d ∧ ringKrullDim R = n := by
  have hbot : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  have htop : ringKrullDim R ≠ ⊤ := ringKrullDim_ne_top
  let n : ℕ := ((ringKrullDim R).unbot hbot).toNat
  have hneTop : (ringKrullDim R).unbot hbot ≠ ⊤ := by
    intro htop'
    exact htop <| by
      simpa [WithBot.coe_unbot] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) htop'
  have hdim : ringKrullDim R = n := by
    have hdim' : ((ringKrullDim R).unbot hbot : WithBot ℕ∞) = n := by
      simpa [n] using
        congrArg (fun x : ℕ∞ ↦ (x : WithBot ℕ∞)) (ENat.coe_toNat hneTop).symm
    calc
      ringKrullDim R = (ringKrullDim R).unbot hbot :=
        (WithBot.coe_unbot (ringKrullDim R) hbot).symm
      _ = n := hdim'
  exact ⟨n, by simpa [hdim] using h, hdim⟩

omit [IsNoetherianRing R] in
private theorem spanFinrank_maximalIdeal_le_one
    (hprincipal : (maximalIdeal R).IsPrincipal) :
    (maximalIdeal R).spanFinrank ≤ 1 := by
  obtain ⟨x, hx⟩ := hprincipal.principal
  rw [hx]
  calc
    (Ideal.span ({x} : Set R)).spanFinrank ≤ ({x} : Set R).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite {x})
    _ = 1 := by simp

/-- A Noetherian local ring with principal maximal ideal that is not Artinian has Krull
dimension one.  No domain hypothesis is needed. -/
@[stacks 0BHZ "principal maximal ideal gives dimension one"]
theorem krullDim_eq_one_of_not_isArtinian
    (hprincipal : (maximalIdeal R).IsPrincipal) (hnot_artinian : ¬ IsArtinianRing R) :
    ringKrullDim R = 1 := by
  -- Local instance justification (proof-local temporary data): derived from non-Artinianness for this contradiction.
  haveI : Nontrivial R := by
    by_contra h
    -- Local instance justification (proof-local temporary data): negated nontriviality supplies this contradiction instance.
    letI : Subsingleton R := not_nontrivial_iff_subsingleton.mp h
    exact hnot_artinian inferInstance
  have hspan := spanFinrank_maximalIdeal_le_one hprincipal
  have hdim_le : ringKrullDim R ≤ 1 :=
    (ringKrullDim_le_spanFinrank_maximalIdeal (R := R)).trans (by exact_mod_cast hspan)
  obtain ⟨n, hn_le, hdim⟩ := exists_nat_ringKrullDim_eq_of_le hdim_le
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    have hdim_zero : ringKrullDim R = 0 := by simpa [hn_zero] using hdim
    have hdim_le_zero : Ring.KrullDimLE 0 R :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim_zero
    exact hnot_artinian <|
      (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2
        ⟨inferInstance, hdim_le_zero⟩
  have hn_one : n = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le with hn_zero | hn_one
    · exact (hn_ne_zero hn_zero).elim
    · exact hn_one
  simpa [hn_one] using hdim

/-- A Noetherian local ring with principal maximal ideal that is not Artinian is regular local.
This is deliberately separate from the dimension statement so consumers can request the exact
conclusion they need. -/
@[stacks 0BHZ "principal maximal ideal gives regularity"]
theorem isRegular_of_not_isArtinian
    (hprincipal : (maximalIdeal R).IsPrincipal) (hnot_artinian : ¬ IsArtinianRing R) :
    IsRegularLocalRing R := by
  have hspan := spanFinrank_maximalIdeal_le_one hprincipal
  have hdim := krullDim_eq_one_of_not_isArtinian hprincipal hnot_artinian
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ↑(maximalIdeal R).spanFinrank ≤ (1 : WithBot ℕ∞) := by exact_mod_cast hspan
    _ = ringKrullDim R := hdim.symm

end

end IsLocalRing.PrincipalMaximalIdeal
