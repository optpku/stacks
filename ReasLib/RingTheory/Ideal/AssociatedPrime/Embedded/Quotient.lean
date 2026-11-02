/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded
public import ReasLib.RingTheory.Support.Cyclic

@[expose] public section

/-!
# Removing Embedded Associated Primes

@stack 02M6

This leaf owns the canonical largest submodule with nowhere-dense support and
the embedded-prime-free quotient it determines.
-/

universe u v

open PrimeSpectrum TopologicalSpace

namespace Module

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The elements whose cyclic support lies in the union of the zero loci of the embedded
associated primes of `M`. -/
@[stacks 02M6 "canonical nowhere-dense submodule"]
def embeddedPrimeFreeSubmodule : Submodule R M where
  carrier := {m | Module.support R (R ∙ m) ⊆
    ⋃ p ∈ embeddedAssociatedPrimes R M, PrimeSpectrum.zeroLocus p}
  zero_mem' := by
    intro p hp
    rw [mem_support_span_singleton_iff_mkLinearMap_ne_zero] at hp
    exact (hp (map_zero _)).elim
  add_mem' := by
    intro x y hx hy p hp
    by_cases hxp : p ∈ Module.support R (R ∙ x)
    · exact hx hxp
    · apply hy
      rw [mem_support_span_singleton_iff_mkLinearMap_ne_zero] at hxp hp ⊢
      push Not at hxp
      simpa only [map_add, hxp, zero_add] using hp
  smul_mem' := by
    intro a x hx p hp
    apply hx
    rw [mem_support_span_singleton_iff_mkLinearMap_ne_zero] at hp ⊢
    intro hzero
    exact hp (by rw [map_smul, hzero, smul_zero])

namespace embeddedPrimeFreeSubmodule

/-- Membership in the canonical submodule is the source cyclic-support condition. -/
@[stacks 02M6 "membership in the canonical nowhere-dense submodule"]
theorem mem_iff (m : M) :
    m ∈ embeddedPrimeFreeSubmodule R M ↔
      Module.support R (R ∙ m) ⊆
        ⋃ p ∈ embeddedAssociatedPrimes R M, PrimeSpectrum.zeroLocus p := Iff.rfl

private theorem finite_closed_nowhereDense_union {ι X : Type*} [TopologicalSpace X]
    {t : Set ι} (ht : t.Finite) (f : ι → Set X)
    (hf : ∀ i ∈ t, IsClosed (f i) ∧ IsNowhereDense (f i)) :
    IsClosed (⋃ i ∈ t, f i) ∧ IsNowhereDense (⋃ i ∈ t, f i) := by
  classical
  revert hf
  induction t, ht using Set.Finite.induction_on with
  | empty => simp
  | @insert i t hi ht ih =>
    intro hf
    rw [Set.biUnion_insert]
    have hfi := hf i (Set.mem_insert i t)
    have hft := ih (fun j hj ↦ hf j (Set.mem_insert_of_mem _ hj))
    refine ⟨hfi.1.union hft.1, ?_⟩
    rw [(hfi.1.union hft.1).isNowhereDense_iff,
      interior_union_isClosed_of_interior_empty hfi.1
        (hft.1.isNowhereDense_iff.mp hft.2), hfi.1.isNowhereDense_iff.mp hfi.2]

variable [IsNoetherianRing R] [Module.Finite R M]

private theorem support_eq_union_associated_zeroLoci :
    Module.support R M =
      ⋃ p ∈ associatedPrimesOfModule R M, PrimeSpectrum.zeroLocus (p : Set R) := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
      (Module.annihilator_le_of_mem_support hp)
    have hqass : q ∈ associatedPrimesOfModule R M := by
      rw [associatedPrimesOfModule_eq_associatedPrimes]
      exact Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq
    exact Set.mem_iUnion₂.mpr ⟨q, hqass, hqp⟩
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Set.mem_iUnion₂.mp hp
    exact Module.mem_support_mono (p := ⟨q, hq.1⟩) hqp
      (associatedPrimesOfModule.subset_support R M hq)

/-- The canonical submodule is maximal among submodules whose relative support is nowhere dense
in the support of `M`. -/
@[stacks 02M6 "maximal nowhere-dense submodule"]
theorem isMaximal_nowhereDense :
    Maximal
      (fun K : Submodule R M ↦
        IsNowhereDense
          {p : Module.support R M | (p : PrimeSpectrum R) ∈ Module.support R K})
      (embeddedPrimeFreeSubmodule R M) := by
  classical
  let K := Module.embeddedPrimeFreeSubmodule R M
  let S := Module.support R M
  let T := associatedPrimesOfModule R M
  let E := embeddedAssociatedPrimes R M
  have hTfinite : T.Finite := by
    change (associatedPrimesOfModule R M).Finite
    rw [associatedPrimesOfModule_eq_associatedPrimes]
    exact associatedPrimes.finite R M
  have hEfinite : E.Finite := hTfinite.subset (fun p hp ↦ hp.1)
  have hZ := finite_closed_nowhereDense_union hEfinite
      (fun p ↦ {s : S | p ≤ (s : PrimeSpectrum R).asIdeal}) (by
    intro p hp
    have hclosed : IsClosed {s : S | p ≤ (s : PrimeSpectrum R).asIdeal} :=
      (PrimeSpectrum.isClosed_zeroLocus (p : Set R)).preimage continuous_subtype_val
    refine ⟨hclosed, hclosed.isNowhereDense_iff.mpr ?_⟩
    obtain ⟨q, hq, hqp, hpq⟩ :
        ∃ q ∈ T, q ≤ p ∧ ¬ p ≤ q := by
      by_contra h
      apply hp.2
      refine ⟨hp.1, ?_⟩
      intro q hq hle
      by_contra hnle
      exact h ⟨q, hq, hle, hnle⟩
    let q0 : PrimeSpectrum R := ⟨q, hq.1⟩
    have hqS : q0 ∈ Module.support R M :=
      associatedPrimesOfModule.subset_support R M hq
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hps : p ≤ (s : PrimeSpectrum R).asIdeal := interior_subset hs
    have hsp : q0 ⤳ (s : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (hqp.trans hps)
    have hspS : (⟨q0, hqS⟩ : S) ⤳ s := (subtype_specializes_iff _ _).mpr hsp
    exact hpq (interior_subset (hspS.mem_open isOpen_interior hs)))
  have hKsubset : {s : S | (s : PrimeSpectrum R) ∈ Module.support R K} ⊆
      ⋃ p ∈ E, {s : S | p ≤ (s : PrimeSpectrum R).asIdeal} := by
    intro s hs
    obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hs
    have hcyc : (s : PrimeSpectrum R) ∈ Module.support R (R ∙ (m : M)) := by
      rw [Module.mem_support_span_singleton_iff_mkLinearMap_ne_zero]
      intro hmzero
      have hmker : (m : M) ∈ LinearMap.ker
          (LocalizedModule.mkLinearMap (s : PrimeSpectrum R).asIdeal.primeCompl M) := hmzero
      obtain ⟨r, hr, hzero⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp hmker
      exact hm r hr (Subtype.ext hzero)
    obtain ⟨p, hp, hps⟩ := Set.mem_iUnion₂.mp (m.property hcyc)
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hps⟩
  refine ⟨IsNowhereDense.mono hKsubset hZ.2, ?_⟩
  intro N hN _ m hmN
  change Module.support R (R ∙ m) ⊆
    ⋃ p ∈ embeddedAssociatedPrimes R M, PrimeSpectrum.zeroLocus (p : Set R)
  intro p hp
  rw [support_eq_union_associated_zeroLoci R (R ∙ m)] at hp
  obtain ⟨q, hq, hqp⟩ := Set.mem_iUnion₂.mp hp
  have hqM : q ∈ T := Ideal.isAssociatedToModule_map_of_injective R (R ∙ m) hq
    (Submodule.subtype _) Subtype.val_injective
  by_cases hqmin : Minimal (· ∈ T) q
  · exfalso
    let q0 : PrimeSpectrum R := ⟨q, hqM.1⟩
    have hqS : q0 ∈ Module.support R M :=
      associatedPrimesOfModule.subset_support R M hqM
    have hspanN : R ∙ m ≤ N := Submodule.span_le.mpr (by simpa using hmN)
    have hqN : q0 ∈ Module.support R N :=
      Module.support_subset_of_injective (Submodule.inclusion hspanN)
        (Submodule.inclusion_injective hspanN)
        (associatedPrimesOfModule.subset_support R (R ∙ m) hq)
    let T' : Set (Ideal R) := {r ∈ T | ¬ q ≤ r}
    let W := ⋃ r ∈ T', PrimeSpectrum.zeroLocus (r : Set R)
    have hT'finite : T'.Finite := hTfinite.subset (fun r hr ↦ hr.1)
    have hWclosed : IsClosed W :=
      hT'finite.isClosed_biUnion (fun r _ ↦ PrimeSpectrum.isClosed_zeroLocus _)
    have hWq : q0 ∉ W := by
      intro h
      obtain ⟨r, hr, hrq⟩ := Set.mem_iUnion₂.mp h
      exact hr.2 (hqmin.2 hr.1 hrq)
    have hopen : IsOpen {s : S | (s : PrimeSpectrum R) ∉ W} :=
      hWclosed.isOpen_compl.preimage continuous_subtype_val
    have hsub : {s : S | (s : PrimeSpectrum R) ∉ W} ⊆
        {s : S | (s : PrimeSpectrum R) ∈ Module.support R N} := by
      intro s hs
      have hsSupp : (s : PrimeSpectrum R) ∈ Module.support R M := s.property
      rw [support_eq_union_associated_zeroLoci R M] at hsSupp
      obtain ⟨r, hr, hrs⟩ := Set.mem_iUnion₂.mp hsSupp
      have hqr : q ≤ r := by
        by_contra hnqr
        exact hs (Set.mem_iUnion₂.mpr ⟨r, ⟨hr, hnqr⟩, hrs⟩)
      exact Module.mem_support_mono (hqr.trans hrs) hqN
    have hint := interior_maximal (hsub.trans subset_closure) hopen
      (show (⟨q0, hqS⟩ : S) ∈ {s : S | (s : PrimeSpectrum R) ∉ W} from hWq)
    rw [hN] at hint
    exact hint
  · exact Set.mem_iUnion₂.mpr ⟨q, ⟨hqM, hqmin⟩, hqp⟩

/-- Quotienting by the canonical submodule preserves support. -/
@[stacks 02M6 "support of the embedded-prime-free quotient"]
theorem support_quotient :
    Module.support R (M ⧸ embeddedPrimeFreeSubmodule R M) = Module.support R M := by
  let K := embeddedPrimeFreeSubmodule R M
  apply Set.Subset.antisymm (Module.support_subset_of_surjective K.mkQ K.mkQ_surjective)
  intro p hp
  by_contra hpq
  let S := Module.support R M
  let A : Set S := {p | (p : PrimeSpectrum R) ∈ Module.support R K}
  let B : Set S := {p | (p : PrimeSpectrum R) ∈ Module.support R (M ⧸ K)}
  have hA : IsNowhereDense A := (isMaximal_nowhereDense R M).prop
  have hB : IsClosed B := (Module.isClosed_support (M := M ⧸ K)).preimage
    continuous_subtype_val
  have hcover := Module.support_of_exact (LinearMap.exact_subtype_mkQ K)
    Subtype.val_injective K.mkQ_surjective
  have hsub : Bᶜ ⊆ closure A := by
    intro q hq
    apply subset_closure
    have hqM : (q : PrimeSpectrum R) ∈ Module.support R M := q.property
    rw [hcover] at hqM
    exact hqM.resolve_right hq
  have hmem := interior_maximal hsub hB.isOpen_compl (show (⟨p, hp⟩ : S) ∈ Bᶜ from hpq)
  rw [hA] at hmem
  exact hmem

/-- The quotient by the canonical submodule has no embedded associated primes. -/
@[stacks 02M6 "embedded associated primes of the quotient"]
theorem embeddedAssociatedPrimes_quotient :
    embeddedAssociatedPrimes R (M ⧸ embeddedPrimeFreeSubmodule R M) = ∅ := by
  let K := embeddedPrimeFreeSubmodule R M
  let Q := M ⧸ K
  let S := Module.support R M
  let A : Set S := {p | (p : PrimeSpectrum R) ∈ Module.support R K}
  have hKmax := isMaximal_nowhereDense R M
  have hAclosed : IsClosed A := (Module.isClosed_support (M := K)).preimage
    continuous_subtype_val
  have hAint : interior A = ∅ := hAclosed.isNowhereDense_iff.mp hKmax.prop
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro q ⟨hq, hqnot⟩
  apply hqnot
  refine ⟨hq, ?_⟩
  intro q' hq' hle
  by_contra hnle
  rcases hq with ⟨hqprime, mbar, hmbar⟩
  let q0 : PrimeSpectrum R := ⟨q', hq'.1⟩
  have hq0supp : q0 ∈ Module.support R M := by
    exact Module.support_subset_of_surjective K.mkQ K.mkQ_surjective
      (associatedPrimesOfModule.subset_support R Q hq')
  -- The smaller associated prime generalizes every point of this relative zero locus.
  let Z : Set S := {p | q ≤ (p : PrimeSpectrum R).asIdeal}
  have hZclosed : IsClosed Z := (PrimeSpectrum.isClosed_zeroLocus (q : Set R)).preimage
    continuous_subtype_val
  have hZint : interior Z = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hqp : q ≤ (p : PrimeSpectrum R).asIdeal := interior_subset hp
    have hsp : q0 ⤳ (p : PrimeSpectrum R) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp (hle.trans hqp)
    have hspS : (⟨q0, hq0supp⟩ : S) ⤳ p :=
      (subtype_specializes_iff _ _).mpr hsp
    exact hnle (interior_subset (hspS.mem_open isOpen_interior hp))
  -- Pulling back the cyclic submodule gives a larger submodule with nowhere-dense support.
  let C := R ∙ mbar
  let N := C.comap K.mkQ
  have hKN : K ≤ N := K.le_comap_mkQ C
  let i : K →ₗ[R] N := Submodule.inclusion hKN
  let g : N →ₗ[R] C :=
    (K.mkQ.comp N.subtype).codRestrict C (fun x ↦ x.property)
  have hiexact : Function.Exact i g := by
    intro x
    constructor
    · intro hx
      have hzero : K.mkQ (x : M) = 0 := congrArg (fun y : C ↦ (y : Q)) hx
      have hxK : (x : M) ∈ K := by
        have hxker : (x : M) ∈ LinearMap.ker K.mkQ := hzero
        simpa only [Submodule.ker_mkQ] using hxker
      exact ⟨⟨(x : M), hxK⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      change K.mkQ (x : M) = 0
      have hxker : (x : M) ∈ LinearMap.ker K.mkQ := by
        rw [Submodule.ker_mkQ]
        exact x.property
      exact hxker
  have hgsurj : Function.Surjective g := by
    intro x
    obtain ⟨m, hm⟩ := K.mkQ_surjective (x : Q)
    refine ⟨⟨m, ?_⟩, Subtype.ext hm⟩
    change K.mkQ m ∈ C
    rw [hm]
    exact x.property
  have hsupportN : Module.support R N = Module.support R K ∪ Module.support R C :=
    Module.support_of_exact hiexact
      (fun x y h ↦ Subtype.ext (congrArg (fun z : N ↦ (z : M)) h)) hgsurj
  have hsupportC : Module.support R C = PrimeSpectrum.zeroLocus (q : Set R) := by
    ext p
    rw [mem_support_span_singleton_iff_mkLinearMap_ne_zero,
      LocalizedModule.mkLinearMap_apply_ne_zero_iff_torsionOf_le, ← hmbar]
    rfl
  have hNclosed : IsClosed {p : S | (p : PrimeSpectrum R) ∈ Module.support R N} :=
    (Module.isClosed_support (M := N)).preimage continuous_subtype_val
  have hNnd : IsNowhereDense {p : S | (p : PrimeSpectrum R) ∈ Module.support R N} := by
    rw [hNclosed.isNowhereDense_iff]
    have hsets : {p : S | (p : PrimeSpectrum R) ∈ Module.support R N} = A ∪ Z := by
      rw [hsupportN, hsupportC]
      rfl
    rw [hsets, interior_union_isClosed_of_interior_empty hAclosed hZint, hAint]
  have hNK : N ≤ K := hKmax.2 hNnd hKN
  obtain ⟨m, hm⟩ := K.mkQ_surjective mbar
  have hmN : m ∈ N := by
    change K.mkQ m ∈ C
    rw [hm]
    exact Submodule.mem_span_singleton_self _
  have hmzero : mbar = 0 := by
    rw [← hm]
    have hmker : m ∈ LinearMap.ker K.mkQ := by
      rw [Submodule.ker_mkQ]
      exact hNK hmN
    exact hmker
  exact hqprime.ne_top (by rw [hmbar, hmzero, Ideal.torsionOf_zero])

/-- Away from an element contained in every embedded associated prime, the quotient map becomes
an isomorphism after localization. -/
@[stacks 02M6 "localization of the embedded-prime-free quotient map"]
theorem localized_quotientMap_bijective (f : R)
    (hf : ∀ p ∈ embeddedAssociatedPrimes R M, f ∈ p) :
    Function.Bijective
      (LocalizedModule.map (.powers f) (embeddedPrimeFreeSubmodule R M).mkQ) := by
  let K := embeddedPrimeFreeSubmodule R M
  have hK : Subsingleton (LocalizedModule (.powers f) K) :=
    LocalizedModule.subsingleton_iff.mpr fun m ↦ by
      have hcyc : Subsingleton (LocalizedModule.Away f (R ∙ (m : M))) :=
        LocalizedModule.subsingleton_iff_support_subset.mpr fun p hp ↦ by
          obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp (m.property hp)
          exact fun r hr ↦ by
            obtain rfl := Set.mem_singleton_iff.mp hr
            exact hpq (hf q hq)
      obtain ⟨r, hr, hz⟩ := LocalizedModule.subsingleton_iff.mp hcyc
        ⟨(m : M), Submodule.mem_span_singleton_self _⟩
      have hval : r • (m : M) = 0 :=
        congrArg (fun x : R ∙ (m : M) ↦ (x : M)) hz
      exact ⟨r, hr, Subtype.ext hval⟩
  letI := hK
  have hex := LocalizedModule.map_exact (.powers f) K.subtype K.mkQ
    (LinearMap.exact_subtype_mkQ K)
  refine ⟨?_, IsLocalizedModule.map_surjective (.powers f) _ _ _ K.mkQ_surjective⟩
  intro x y hxy
  have hz : LocalizedModule.map (.powers f) K.mkQ (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (hex (x - y)).mp hz
  have hz' : x - y = 0 := hz.symm.trans (by rw [Subsingleton.elim z 0, map_zero])
  exact sub_eq_zero.mp hz'

end embeddedPrimeFreeSubmodule
end Module
