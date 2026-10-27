/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Valuation.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete valuation ring characterizations

The primary interfaces in this leaf use the canonical typeclass assumptions for a Noetherian
local domain.  The existentially packaged TFAE from the chapter is retained below as a
source-facing bridge, so downstream developments can choose either the short canonical iff
statements or the literal list of alternatives.

@stack 09DZ
@stack 00PD
-/

@[expose] public section

universe u

open Ideal IsLocalRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- Definition 10.119.8 (Stacks `09DZ`): a uniformizer is an element generating the maximal
ideal; the canonical DVR owner expresses this by irreducibility. -/
@[stacks 09DZ]
theorem maximalIdeal_eq_span_singleton_iff_irreducible (π : A) :
    maximalIdeal A = Ideal.span {π} ↔ Irreducible π :=
  (irreducible_iff_uniformizer π).symm

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The canonical DVR criterion: a Noetherian local domain is a DVR exactly when it is regular
local of Krull dimension one. -/
@[stacks 00PD "regular-local characterization"]
theorem iff_regularLocalRing_dim_one :
    IsDiscreteValuationRing A ↔ IsRegularLocalRing A ∧ ringKrullDim A = 1 := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, ringKrullDim_eq_one A⟩
  · rintro ⟨hreg, hdim⟩
    letI := hreg
    apply finrank_CotangentSpace_eq_one_iff.mp
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp hreg
    rw [hdim] at h
    exact_mod_cast h

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]

/-- A nonzero principal maximal ideal is equivalent to the DVR condition.  The nonzero clause is
kept in the proposition so callers do not have to manufacture a separate `¬ IsField A` witness. -/
@[stacks 00PD "principal maximal ideal characterization"]
theorem iff_maximalIdeal_isPrincipal :
    IsDiscreteValuationRing A ↔
      maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal := by
  constructor
  · intro h
    letI := h
    exact ⟨not_a_field A, inferInstance⟩
  · intro h
    exact ((TFAE A (isField_iff_maximalIdeal_eq.not.mpr h.1)).out 4 0).mp h.2

/-- A Noetherian local domain is a DVR exactly when it is normal and one-dimensional. -/
@[stacks 00PD "normal dimension-one characterization"]
theorem iff_integrallyClosed_dim_one :
    IsDiscreteValuationRing A ↔ IsIntegrallyClosed A ∧ ringKrullDim A = 1 := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, ringKrullDim_eq_one A⟩
  · rintro ⟨hclosed, hdim⟩
    letI := hclosed
    letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simp [hdim])
    have hfield : ¬ IsField A := fun h ↦
      zero_ne_one ((ringKrullDim_eq_zero_of_isField h) ▸ hdim)
    apply ((TFAE A hfield).out 3 0).mp
    refine ⟨hclosed, maximalIdeal A,
      ⟨isField_iff_maximalIdeal_eq.not.mp hfield, inferInstance⟩, ?_⟩
    rintro P ⟨hP, hprime⟩
    exact eq_maximalIdeal (hprime.isMaximal_of_ne_bot hP)

/-- Construct a DVR from the normal one-dimensional local-domain criterion. -/
@[stacks 00PD "normal dimension-one construction"]
theorem of_integrallyClosed_dim_one [IsIntegrallyClosed A]
    (hdim : ringKrullDim A = 1) : IsDiscreteValuationRing A :=
  iff_integrallyClosed_dim_one.mpr ⟨inferInstance, hdim⟩

/-- Construct a DVR from a nonzero principal maximal ideal in a Noetherian local domain. -/
@[stacks 00PD "principal maximal ideal construction"]
theorem of_maximalIdeal_isPrincipal
    (h : maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal) :
    IsDiscreteValuationRing A :=
  iff_maximalIdeal_isPrincipal.mpr h

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsDomain A]

/-- A regular local ring of Krull dimension one is a DVR.  The regular-local structure is accepted
as a proposition argument so callers holding a term need not install a temporary local instance. -/
@[stacks 00PD "regular-local construction"]
theorem of_regularLocalRing_dim_one
    (hreg : IsRegularLocalRing A) (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A :=
  iff_regularLocalRing_dim_one.mpr ⟨hreg, hdim⟩

end IsDiscreteValuationRing

/-- Krull intersection gives a unit-times-power expression even before proving the ring is a domain. -/
private theorem exists_unit_mul_pow_of_span_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {π a : A} (hπ : maximalIdeal A = Ideal.span {π}) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : Aˣ), a = (u : A) * π ^ n := by
  classical
  have hex : ∃ n : ℕ, a ∉ maximalIdeal A ^ n := by
    by_contra! h
    apply ha
    have hmem : a ∈ ⨅ n : ℕ, maximalIdeal A ^ n := by
      simpa only [Submodule.mem_iInf] using h
    simpa only [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top,
      Submodule.mem_bot] using hmem
  obtain ⟨n, hn, hn'⟩ : ∃ n : ℕ,
      a ∈ maximalIdeal A ^ n ∧ a ∉ maximalIdeal A ^ (n + 1) := by
    rcases hn : Nat.find hex with - | n
    · have h := Nat.find_spec hex
      simp [hn] at h
    · refine ⟨n, ?_, ?_⟩
      · show a ∈ maximalIdeal A ^ n
        exact not_not.mp (Nat.find_min hex (by rw [hn]; exact Nat.lt_succ_self n))
      · show a ∉ maximalIdeal A ^ (n + 1)
        simpa only [hn] using Nat.find_spec hex
  have hπmem : π ∈ maximalIdeal A := hπ.symm ▸ Ideal.subset_span (Set.mem_singleton π)
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn
  obtain ⟨b, hb⟩ := hn
  have hbunit : IsUnit b := by
    by_contra h
    apply hn'
    rw [hb, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπmem n) h
  obtain ⟨u, rfl⟩ := hbunit
  exact ⟨n, u, hb.trans (mul_comm _ _)⟩

/-- A principal maximal ideal in dimension one has a nonnilpotent generator. -/
private theorem isDomain_of_span_maximalIdeal_dim_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {π : A} (hπ : maximalIdeal A = Ideal.span {π}) (hdim : ringKrullDim A = 1) :
    IsDomain A := by
  have hnil : ¬ IsNilpotent π := by
    intro h
    have hzero : Ring.KrullDimLE 0 A := Ring.KrullDimLE.mk₀ fun P hP ↦ by
      letI := hP
      have hle : maximalIdeal A ≤ P := by
        rw [hπ]
        exact (Ideal.span_singleton_le_iff_mem P).mpr (nilradical_le_prime P (mem_nilradical.mpr h))
      have heq := (maximalIdeal.isMaximal A).eq_of_le hP.ne_top hle
      exact heq ▸ maximalIdeal.isMaximal A
    exact zero_ne_one ((ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hzero) ▸ hdim)
  letI : NoZeroDivisors A := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · show a = 0 ∨ b = 0
      exact Or.inl ha
    by_cases hb : b = 0
    · show a = 0 ∨ b = 0
      exact Or.inr hb
    obtain ⟨n, u, hu⟩ := exists_unit_mul_pow_of_span_maximalIdeal hπ ha
    obtain ⟨m, v, hv⟩ := exists_unit_mul_pow_of_span_maximalIdeal hπ hb
    rw [hu, hv, mul_mul_mul_comm, ← pow_add] at hab
    exact (hnil ⟨n + m, (Units.mul_right_eq_zero (u * v)).mp
      (by simpa only [Units.val_mul] using hab)⟩).elim
  exact (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨inferInstance, inferInstance⟩


variable {A : Type u} [CommRing A]

/-- Lemma 10.119.7 (Stacks `00PD`): the source-facing five-way characterization of a discrete
valuation ring.  The canonical reusable views are the iff theorems in
`IsDiscreteValuationRing`. -/
@[stacks 00PD]
theorem discreteValuationRing_tfae :
    List.TFAE
      [ (∃ (_ : IsDomain A), IsDiscreteValuationRing A),
        ∃ (_ : IsDomain A) (_ : IsNoetherianRing A), ValuationRing A ∧ ¬ IsField A,
        IsRegularLocalRing A ∧ ringKrullDim A = 1,
        ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A),
          maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal,
        ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
          (_ : IsIntegrallyClosed A), ringKrullDim A = 1 ] := by
  tfae_have 1 → 2 := by
    rintro ⟨hdom, hdvr⟩
    letI := hdom
    letI := hdvr
    exact ⟨hdom, inferInstance, inferInstance, IsDiscreteValuationRing.not_isField A⟩
  tfae_have 2 → 1 := by
    rintro ⟨hdom, hnoeth, hval, hfield⟩
    letI := hdom
    letI := hnoeth
    letI := hval
    exact ⟨hdom, ((IsDiscreteValuationRing.TFAE A hfield).out 1 0).mp hval⟩
  tfae_have 1 → 3 := by
    rintro ⟨hdom, hdvr⟩
    letI := hdom
    exact IsDiscreteValuationRing.iff_regularLocalRing_dim_one.mp hdvr
  tfae_have 3 → 1 := by
    rintro ⟨hreg, hdim⟩
    letI := hreg
    have hrank : Module.finrank (ResidueField A) (CotangentSpace A) = 1 := by
      have h := (IsRegularLocalRing.iff_finrank_cotangentSpace A).mp hreg
      rw [hdim] at h
      exact_mod_cast h
    have hprincipal := finrank_cotangentSpace_le_one_iff.mp hrank.le
    obtain ⟨π, hπ⟩ := hprincipal.principal
    letI : IsDomain A := isDomain_of_span_maximalIdeal_dim_one hπ hdim
    exact ⟨inferInstance, IsDiscreteValuationRing.of_regularLocalRing_dim_one hreg hdim⟩
  tfae_have 1 → 4 := by
    rintro ⟨hdom, hdvr⟩
    letI := hdom
    letI := hdvr
    exact ⟨inferInstance, inferInstance, hdom,
      IsDiscreteValuationRing.iff_maximalIdeal_isPrincipal.mp hdvr⟩
  tfae_have 4 → 1 := by
    rintro ⟨hlocal, hnoeth, hdom, hprincipal⟩
    letI := hlocal
    letI := hnoeth
    letI := hdom
    exact ⟨hdom, IsDiscreteValuationRing.of_maximalIdeal_isPrincipal hprincipal⟩
  tfae_have 1 → 5 := by
    rintro ⟨hdom, hdvr⟩
    letI := hdom
    letI := hdvr
    exact ⟨inferInstance, inferInstance, hdom, inferInstance,
      IsDiscreteValuationRing.ringKrullDim_eq_one A⟩
  tfae_have 5 → 1 := by
    rintro ⟨hlocal, hnoeth, hdom, hclosed, hdim⟩
    letI := hlocal
    letI := hnoeth
    letI := hdom
    letI := hclosed
    exact ⟨hdom, IsDiscreteValuationRing.of_integrallyClosed_dim_one hdim⟩
  tfae_finish

/-- Source bridge for the regular-local clause of Lemma 10.119.7, retaining the chapter's
existential domain packaging. -/
@[stacks 00PD "source regular-local bridge"]
theorem discreteValuationRing_iff_regularLocalRing_dim_one :
    (∃ (_ : IsDomain A), IsDiscreteValuationRing A) ↔
      IsRegularLocalRing A ∧ ringKrullDim A = 1 :=
  discreteValuationRing_tfae.out 0 2

variable [IsDomain A] [IsDiscreteValuationRing A]

namespace IsDiscreteValuationRing

/-- Every nonzero element of a DVR has a unique unit-times-power normal form for a chosen
generator of the maximal ideal. -/
@[stacks 00PD "uniformizer normal form"]
theorem existsUnique_unit_mul_pow (π a : A)
    (hπ : maximalIdeal A = Ideal.span {π}) (ha : a ≠ 0) :
    ∃! p : Aˣ × ℕ, a = (p.1 : A) * π ^ p.2 := by
  have hirr := (maximalIdeal_eq_span_singleton_iff_irreducible π).mp hπ
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible ha hirr
  refine ⟨(u, n), hu, ?_⟩
  rintro ⟨v, m⟩ hv
  have h : (v : A) * π ^ m = (u : A) * π ^ n := hv.symm.trans hu
  exact Prod.ext (unit_mul_pow_congr_unit hirr v u m n h)
    (unit_mul_pow_congr_pow hirr hirr v u m n h)

end IsDiscreteValuationRing
