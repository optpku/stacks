/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.LinearCombination

/-!
# Prime-ideal factorizations in Dedekind domains

This file separates finite prime-ideal factorizations from the Dedekind-domain characterization
that they induce.  The factorization predicates are available over commutative semirings, while
Stacks `034W` is a proved characterization of Mathlib's canonical `IsDedekindDomain` owner,
and `034X` gives its Noetherian normal and local-DVR characterizations. Fields are included.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- A multiset is a prime factorization of an ideal when all of its entries are nonzero prime
ideals and their product is the given ideal. -/
@[stacks 034W "prime factorization"]
def IsPrimeFactorization (I : Ideal R) (f : Multiset (Ideal R)) : Prop :=
  (∀ P ∈ f, P ≠ ⊥ ∧ P.IsPrime) ∧ f.prod = I

namespace IsPrimeFactorization

/-- Every factor occurring in a prime factorization is nonzero. -/
@[stacks 034W "nonzero factor"]
theorem ne_bot_of_mem {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) (hP : P ∈ f) : P ≠ ⊥ := sorry

/-- Every factor occurring in a prime factorization is a prime ideal. -/
@[stacks 034W "prime factor"]
theorem isPrime_of_mem {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) (hP : P ∈ f) : P.IsPrime := sorry

/-- The product recorded by a prime factorization is the factored ideal. -/
@[stacks 034W "factorization product"]
theorem prod_eq {I : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) : f.prod = I := sorry

/-- A nonzero prime ideal is its own one-term prime factorization. -/
@[stacks 034W "singleton factorization"]
theorem singleton {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) :
    IsPrimeFactorization P {P} := sorry

/-- If a prime ideal contains an ideal represented by a prime factorization, then it contains
one of the factors. -/
@[stacks 034W "factor below a prime"]
theorem exists_le_of_le_prime {I P : Ideal R} {f : Multiset (Ideal R)}
    (hf : IsPrimeFactorization I f) (hP : P.IsPrime) (hIP : I ≤ P) :
    ∃ Q ∈ f, Q ≤ P := sorry

end IsPrimeFactorization

/-- Every nonzero ideal has a unique multiset factorization into nonzero prime ideals. -/
@[stacks 034W "unique prime factorization"]
def HasUniquePrimeFactorization (R : Type u) [CommSemiring R] : Prop :=
  ∀ I : Ideal R, I ≠ ⊥ → ∃! f : Multiset (Ideal R), I.IsPrimeFactorization f

namespace HasUniquePrimeFactorization

/-- Unique prime factorization supplies a prime factorization of each nonzero ideal. -/
@[stacks 034W "factorization existence"]
theorem exists_factorization (h : HasUniquePrimeFactorization R)
    {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ f : Multiset (Ideal R), I.IsPrimeFactorization f := sorry

/-- Two prime factorizations of the same nonzero ideal agree as multisets. -/
@[stacks 034W "factorization uniqueness"]
theorem unique (h : HasUniquePrimeFactorization R) {I : Ideal R}
    (hI : I ≠ ⊥) {f g : Multiset (Ideal R)}
    (hf : I.IsPrimeFactorization f) (hg : I.IsPrimeFactorization g) : f = g := sorry

end HasUniquePrimeFactorization

end Ideal

open scoped nonZeroDivisors

namespace Ideal.HasUniquePrimeFactorization

variable {R : Type*} [CommRing R]

private theorem factor_map_eq (P : Ideal R) [P.IsPrime] (f : Multiset (Ideal R))
    (hf : ∀ Q ∈ f, Q.IsPrime) (hle : f.prod ≤ P) (hnot : ¬ f.prod ≤ P * P) :
    ∃ Q ∈ f, Q ≤ P ∧
      f.prod.map (algebraMap R (Localization.AtPrime P)) =
        Q.map (algebraMap R (Localization.AtPrime P)) := by
  classical
  induction f using Multiset.induction_on with
  | empty =>
    exact False.elim (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)
      (top_le_iff.mp (by simpa using hle)))
  | @cons Q f ih =>
    simp only [Multiset.prod_cons] at hle hnot ⊢
    by_cases hQ : Q ≤ P
    · have hn : ¬ f.prod ≤ P := fun ht ↦ hnot (mul_le_mul' hQ ht)
      refine ⟨Q, by simp, hQ, ?_⟩
      rw [Ideal.map_mul, IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hn,
        ← Ideal.one_eq_top, mul_one]
    · have ht : f.prod ≤ P := ((inferInstance : P.IsPrime).mul_le.mp hle).resolve_left hQ
      obtain ⟨T, hT, hTP, he⟩ := ih (fun T hT ↦ hf T (by simp [hT])) ht
        (fun h ↦ hnot (Ideal.mul_le_left.trans h))
      refine ⟨T, by simp [hT], hTP, ?_⟩
      rw [Ideal.map_mul, IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hQ,
        ← Ideal.one_eq_top, one_mul, he]

private theorem prime_ne_mul_self (h : Ideal.HasUniquePrimeFactorization R)
    {P : Ideal R} (hP0 : P ≠ ⊥) (hP : P.IsPrime) : P * P ≠ P := by
  classical
  intro heq
  have h1 : Ideal.IsPrimeFactorization P {P} := by
    exact ⟨by simpa using And.intro hP0 hP, by simp⟩
  have h2 : Ideal.IsPrimeFactorization P ({P, P} : Multiset (Ideal R)) := by
    exact ⟨by simpa using And.intro hP0 hP, by simpa using heq⟩
  have e := (h P hP0).unique h1 h2
  have ec := congrArg Multiset.card e
  simp at ec

private theorem localization_span_eq (h : Ideal.HasUniquePrimeFactorization R)
    {P : Ideal R} (hP0 : P ≠ ⊥) [hP : P.IsPrime] :
    ∃ x ∈ P, x ∉ P * P ∧ x ≠ 0 ∧
      P.map (algebraMap R (Localization.AtPrime P)) =
        Ideal.span {algebraMap R (Localization.AtPrime P) x} := by
  have hnot : ¬ P ≤ P * P := fun ht ↦
    prime_ne_mul_self h hP0 hP (le_antisymm Ideal.mul_le_right ht)
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp hnot
  have hx0 : x ≠ 0 := fun he ↦ hx2 (he.symm ▸ (P * P).zero_mem)
  let g := algebraMap R (Localization.AtPrime P)
  have hpair (y : R) (hy : y ∈ P) :
      (Ideal.span ({g x, g y} : Set (Localization.AtPrime P))).IsPrime := by
    have hJ : Ideal.span ({x, y} : Set R) ≤ P := Ideal.span_le.mpr (by
      rintro z (rfl | rfl) <;> assumption)
    have hJ0 : Ideal.span ({x, y} : Set R) ≠ ⊥ := by
      intro he
      exact hx0 ((show x ∈ (⊥ : Ideal R) from he ▸ Ideal.subset_span (by simp)))
    obtain ⟨f, hf, _⟩ := h _ hJ0
    obtain ⟨Q, hQ, hQP, he⟩ := factor_map_eq P f (fun Q hQ ↦ (hf.1 Q hQ).2)
      (hf.2.symm ▸ hJ) (fun ht ↦ hx2 (ht (hf.2.symm ▸ Ideal.subset_span (by simp))))
    have hQprime : Q.IsPrime := (hf.1 Q hQ).2
    letI := hQprime
    have hmap := Ideal.isPrime_map_of_isLocalizationAtPrime (S := Localization.AtPrime P) P hQP
    rw [hf.2, Ideal.map_span, Set.image_pair] at he
    exact he.symm ▸ hmap
  refine ⟨x, hx, hx2, hx0, le_antisymm ?_ ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro y hy
    change g y ∈ Ideal.span {g x}
    have hp := hpair (y * y) (P.mul_mem_left y hy)
    have hy2 : g y * g y ∈ Ideal.span ({g x, g (y * y)} : Set (Localization.AtPrime P)) := by
      rw [map_mul]
      exact Ideal.subset_span (by simp)
    have hyJ := (hp.mul_mem_iff_mem_or_mem.mp hy2).elim id id
    obtain ⟨a, b, he⟩ := Ideal.mem_span_pair.mp hyJ
    have hb : b * g y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      apply Ideal.mul_mem_left
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem g hy
    have hu : IsUnit (1 - b * g y) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
        ((IsLocalRing.mem_maximalIdeal _).mp hb)
    apply (Ideal.unit_mul_mem_iff_mem _ hu).mp
    have he' : (1 - b * g y) * g y = a * g x := by
      dsimp [g] at he ⊢
      rw [map_mul] at he
      linear_combination -he
    rw [he']
    exact Ideal.mul_mem_left _ a (Ideal.subset_span (by simp))
  · exact Ideal.span_le.mpr (by
      simp only [Set.singleton_subset_iff]
      exact Ideal.mem_map_of_mem g hx)

private theorem prime_fractional_isUnit [IsDomain R]
    (h : Ideal.HasUniquePrimeFactorization R)
    {P : Ideal R} (hP0 : P ≠ ⊥) [hP : P.IsPrime] :
    IsUnit (P : FractionalIdeal R⁰ (FractionRing R)) := by
  classical
  obtain ⟨x, hx, hx2, hx0, he⟩ := localization_span_eq h hP0
  have hI0 : Ideal.span ({x} : Set R) ≠ ⊥ := by simpa using hx0
  obtain ⟨f, hf, _⟩ := h _ hI0
  obtain ⟨Q, hQ, hQP⟩ := hP.multiset_prod_le.mp
    (hf.2.symm ▸ Ideal.span_le.mpr (by simpa using hx))
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hQ
  have htmap : t.prod.map (algebraMap R (Localization.AtPrime P)) = ⊤ := by
    have hprod : Q * t.prod = Ideal.span {x} := by simpa [ht] using hf.2
    apply IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) (p := P)
    intro htle
    exact hx2 ((mul_le_mul' hQP htle) (hprod.symm ▸ Ideal.subset_span (by simp)))
  have hmap : Q.map (algebraMap R (Localization.AtPrime P)) =
      P.map (algebraMap R (Localization.AtPrime P)) := by
    have hm := congrArg (Ideal.map (algebraMap R (Localization.AtPrime P))) hf.2
    rw [ht, Multiset.prod_cons, Ideal.map_mul, htmap,
      ← Ideal.one_eq_top, mul_one] at hm
    rw [he]
    simpa only [Ideal.map_span, Set.image_singleton] using hm
  letI : Q.IsPrime := (hf.1 Q hQ).2
  have hQP_eq : Q = P := by
    have hc := congrArg (fun I : Ideal (Localization.AtPrime P) ↦ I.under R) hmap
    simpa only [Ideal.under_map_of_isLocalizationAtPrime P hQP,
      Ideal.under_map_of_isLocalizationAtPrime P (le_refl P)] using hc
  have hprod : P * t.prod = Ideal.span {x} := by simpa [ht, hQP_eq] using hf.2
  have hunit : IsUnit ((P : FractionalIdeal R⁰ (FractionRing R)) *
      (t.prod : FractionalIdeal R⁰ (FractionRing R))) := by
    rw [← FractionalIdeal.coeIdeal_mul, hprod]
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mp
      (FractionalIdeal.coe_ideal_span_singleton_mul_inv (FractionRing R) hx0)
  exact isUnit_of_mul_isUnit_left hunit

private theorem ideal_fractional_isUnit [IsDomain R]
    (h : Ideal.HasUniquePrimeFactorization R) {I : Ideal R} (hI : I ≠ ⊥) :
    IsUnit (I : FractionalIdeal R⁰ (FractionRing R)) := by
  obtain ⟨f, hf, _⟩ := h I hI
  rw [← hf.2]
  suffices ∀ f : Multiset (Ideal R), (∀ P ∈ f, P ≠ ⊥ ∧ P.IsPrime) →
      IsUnit (f.prod : FractionalIdeal R⁰ (FractionRing R)) from this f hf.1
  intro f
  induction f using Multiset.induction_on with
  | empty => intro _; simp
  | @cons P f ih =>
    intro hf
    have hp := hf P (by simp)
    letI := hp.2
    rw [Multiset.prod_cons, FractionalIdeal.coeIdeal_mul]
    exact (prime_fractional_isUnit h hp.1).mul
      (ih fun Q hQ ↦ hf Q (by simp [hQ]))

/-- Unique nonzero prime-ideal factorization in a domain implies the canonical
Dedekind-domain conditions, without assuming Noetherianity in advance. -/
theorem isDedekindDomain [IsDomain R] (h : Ideal.HasUniquePrimeFactorization R) :
    IsDedekindDomain R := by
  apply (isDedekindDomain_iff_isDedekindDomainInv).mpr
  intro I hI
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mpr
  obtain ⟨a, J, ha, he⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ ⊥ := by
    intro hz
    simp [hz] at he
    exact hI he
  rw [he]
  apply IsUnit.mul _ (ideal_fractional_isUnit h hJ)
  apply (FractionalIdeal.mul_inv_cancel_iff_isUnit (FractionRing R)).mp
  exact FractionalIdeal.spanSingleton_mul_inv (FractionRing R)
    (inv_ne_zero (map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R _)
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha)))

end Ideal.HasUniquePrimeFactorization

namespace IsDedekindDomain

variable {R : Type u} [CommRing R] [IsDedekindDomain R]

open UniqueFactorizationMonoid

/-- Mathlib's normalized factors of a nonzero ideal form its canonical prime factorization. -/
@[stacks 034W "normalized factors"]
theorem isPrimeFactorization_normalizedFactors {I : Ideal R} (hI : I ≠ ⊥) :
    I.IsPrimeFactorization (normalizedFactors I) := by
  refine ⟨?_, Ideal.prod_normalizedFactors_eq_self hI⟩
  intro P hP
  exact ⟨(prime_of_normalized_factor P hP).ne_zero,
    Ideal.isPrime_of_prime (prime_of_normalized_factor P hP)⟩

/-- The canonical Dedekind-domain owner supplies unique prime factorizations of nonzero ideals. -/
@[stacks 034W "canonical factorization"]
theorem hasUniquePrimeFactorization : Ideal.HasUniquePrimeFactorization R := by
  intro I hI
  refine ⟨normalizedFactors I, isPrimeFactorization_normalizedFactors hI, ?_⟩
  intro f hf
  have hfactors : normalizedFactors f.prod = f :=
    normalizedFactors_prod_of_prime fun P hP ↦
      Ideal.prime_of_isPrime (hf.1 P hP).1 (hf.1 P hP).2
  rw [hf.2] at hfactors
  exact hfactors.symm

end IsDedekindDomain

/-- Definition 10.120.14 (Stacks `034W`): a Dedekind domain is a domain in which every
nonzero ideal factors uniquely, up to permutation, into nonzero prime ideals. -/
@[stacks 034W]
theorem isDedekindDomain_iff_hasUniquePrimeFactorization
    (R : Type u) [CommRing R] :
    IsDedekindDomain R ↔ IsDomain R ∧ Ideal.HasUniquePrimeFactorization R := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, IsDedekindDomain.hasUniquePrimeFactorization⟩
  · rintro ⟨hD, hfactor⟩
    letI := hD
    exact hfactor.isDedekindDomain

/-- Lemma 10.120.17 (1): Mathlib's canonical Dedekind-domain owner is exactly a
Noetherian normal domain of Krull dimension at most one. Fields are included. -/
@[stacks 034X "Noetherian normal characterization"]
theorem isDedekindDomain_iff_noetherian_dimensionLEOne_isIntegrallyClosed
    (R : Type u) [CommRing R] :
    IsDedekindDomain R ↔
      IsDomain R ∧ IsNoetherianRing R ∧ Ring.DimensionLEOne R ∧ IsIntegrallyClosed R := by
  constructor
  · intro h
    letI := h
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hD, hN, hdim, hnormal⟩
    letI := hD
    letI := hN
    letI := hdim
    letI := hnormal
    exact (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨hD, hN, hdim, (isIntegrallyClosed_iff (FractionRing R)).mp hnormal⟩

namespace IsDedekindDomain

variable {R : Type u} [CommRing R]

/-- Lemma 10.120.17 (2): a Dedekind domain is equivalently a Noetherian domain whose
localizations at nonzero maximal ideals are DVRs. The nonzero restriction includes fields. -/
@[stacks 034X "local DVR characterization"]
theorem iff_localizationAtMaximal :
    IsDedekindDomain R ↔
      ∃ (_ : IsDomain R) (_ : IsNoetherianRing R),
        ∀ m : MaximalSpectrum R, m.asIdeal ≠ ⊥ →
          IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) := by
  constructor
  · intro h
    letI := h
    refine ⟨inferInstance, inferInstance, ?_⟩
    intro m hm
    exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hm _
  · rintro ⟨hD, hN, hlocal⟩
    letI := hD
    letI := hN
    have hdim : Ring.DimensionLEOne R := ⟨by
      intro p hp hpp
      rcases p.exists_le_maximal hpp.ne_top with ⟨q, hq, hpq⟩
      let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
      let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
      let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a ↦ a⟩
      have hinj : Function.Injective (algebraMap R (Localization.AtPrime q)) :=
        IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
      have hp1 : P.1 ≠ ⊥ := fun x ↦ hp ((p.map_eq_bot_iff_of_injective hinj).mp x)
      have hq1 : Q.1 ≠ ⊥ :=
        fun x ↦ (ne_bot_of_le_ne_bot hp hpq) ((q.map_eq_bot_iff_of_injective hinj).mp x)
      rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
        (Localization.AtPrime q)).mp
          (hlocal ⟨q, hq⟩ (ne_bot_of_le_ne_bot hp hpq)) with ⟨_, huq⟩
      rw [show p = q from Subtype.val_inj.mpr <| f.injective <|
        Subtype.val_inj.mp (huq.unique ⟨hp1, P.2⟩ ⟨hq1, Q.2⟩)]
      exact hq⟩
    have hnormal : IsIntegrallyClosed R :=
      IsIntegrallyClosed.of_localization_maximal fun p hp hpm ↦ by
        let ⟨_, _⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
          (Localization.AtPrime p)).mp (hlocal ⟨p, hpm⟩ hp)
        infer_instance
    exact (isDedekindDomain_iff_noetherian_dimensionLEOne_isIntegrallyClosed R).mpr
      ⟨hD, hN, hdim, hnormal⟩

end IsDedekindDomain

/-- Under an ambient domain instance, Mathlib's canonical Dedekind-domain owner is equivalent
to its local-DVR characterization. -/
@[stacks 034X "canonical local-DVR bridge"]
theorem isDedekindDomain_iff_isDedekindDomainDvr
    (R : Type u) [CommRing R] [IsDomain R] :
    IsDedekindDomain R ↔ IsDedekindDomainDvr R := by
  constructor <;> intro h <;> letI := h <;> infer_instance
