/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.Separable.Generated.Properties

/-!
# Smooth subalgebra models of separable field extensions

This leaf owns the reusable relation between separability in the
Stacks-project sense and smooth subalgebras with a fixed ambient fraction
field.  Finite-set and directed-family forms are included because they are
the natural downstream interface for approximation arguments.

@stack 037X
@stack 07BV
-/

@[expose] public section

namespace Algebra.IsSeparableOver

universe u v

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- A field extension with a smooth subalgebra whose fraction field is the
ambient field is separable over its base. -/
@[stacks 037X "smooth fraction-field model implies separability"]
theorem of_smooth_subalgebra_isFractionRing
    (A : Subalgebra k K) (hA : Algebra.Smooth k A) (hfrac : IsFractionRing A K) :
    Algebra.IsSeparableOver k K := sorry

/-- An essentially finite-type separable field extension has a smooth
subalgebra whose fraction field is the ambient field. -/
@[stacks 037X "separable extensions admit smooth fraction-field models"]
theorem exists_smooth_subalgebra_isFractionRing
    [Algebra.EssFiniteType k K] [Algebra.IsSeparableOver k K] :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ IsFractionRing A K := by
  letI : Algebra.IsSeparablyGenerated k K := Algebra.IsSeparableOver.isSeparablyGenerated
  obtain ⟨s, hs, hsep⟩ := Algebra.IsSeparablyGenerated.existsSeparatingBasis (k := k) (K := K)
  letI : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range (Subtype.val : s → K))) K := by
    convert! hsep <;> simp only [Subtype.range_val]
  letI : Algebra.FormallySmooth k K :=
    Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1
  obtain ⟨A, M, hft, hloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra k K).mp
    (inferInstance : Algebra.EssFiniteType k K)
  letI := hft
  letI := hloc
  letI : IsFractionRing A K := IsFractionRing.of_field A K fun z => by
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj M z
    refine ⟨a, b, ?_⟩
    exact (eq_div_iff (IsLocalization.map_units K b).ne_zero).mpr hab
  letI : IsLocalization (⊥ : Ideal A).primeCompl K := by
    rw [Ideal.primeCompl_bot]
    infer_instance
  letI : Algebra.IsSmoothAt k (⊥ : Ideal A) :=
    Algebra.FormallySmooth.of_equiv
      ((IsLocalization.algEquiv (⊥ : Ideal A).primeCompl K
        (Localization.AtPrime (⊥ : Ideal A))).restrictScalars k)
  letI : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp hft
  obtain ⟨f, hf, hfs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal A)
  letI := hfs
  let B := Localization.subalgebra K (Submonoid.powers f)
    (Submonoid.powers_le.mpr (by simpa using hf))
  let C := B.restrictScalars k
  letI : Algebra.Smooth k B := Algebra.Smooth.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) B).restrictScalars k)
  letI : Algebra.Smooth k C := by
    change Algebra.Smooth k B
    infer_instance
  refine ⟨C, inferInstance, ?_⟩
  change IsFractionRing B K
  infer_instance

/-- Explicit-hypothesis form of `exists_smooth_subalgebra_isFractionRing`; use this when
separability is available as a proposition value rather than an installed instance. -/
@[stacks 037X "explicit smooth fraction-field model bridge"]
theorem exists_smooth_subalgebra_isFractionRing_of [Algebra.EssFiniteType k K]
    (hsep : Algebra.IsSeparableOver k K) :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ IsFractionRing A K := by
  letI := hsep
  exact exists_smooth_subalgebra_isFractionRing

/-- An essentially finite-type field extension is separable over its base
exactly when it has a smooth subalgebra with the given fraction field. -/
@[stacks 037X]
theorem iff_exists_smooth_subalgebra_isFractionRing [Algebra.EssFiniteType k K] :
    Algebra.IsSeparableOver k K ↔
      ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ IsFractionRing A K := by
  constructor
  · exact exists_smooth_subalgebra_isFractionRing_of
  · rintro ⟨A, hA, hfrac⟩
    exact of_smooth_subalgebra_isFractionRing A hA hfrac

/-- Every finite subset of a separable field extension lies in a smooth
subalgebra over the base field. -/
@[stacks 07BV "finite smooth subalgebra cover"]
theorem exists_smooth_subalgebra_containing_finset [Algebra.IsSeparableOver k K]
    (E : Finset K) :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ (E : Set K) ⊆ A := by
  let L := IntermediateField.adjoin k (E : Set K)
  letI : Algebra.EssFiniteType k L := IntermediateField.essFiniteType_iff.mpr
    (IntermediateField.fg_adjoin_of_finite E.finite_toSet)
  letI : Algebra.IsSeparableOver k L := of_intermediateField L
  obtain ⟨A, hA, hfrac⟩ := exists_smooth_subalgebra_isFractionRing (k := k) (K := L)
  letI := hA
  letI := hfrac
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun x : E => (⟨x, IntermediateField.subset_adjoin k (E : Set K) x.property⟩ : L))
  let B := Localization.subalgebra.ofField L (Submonoid.powers (b : A))
    (Submonoid.powers_le.mpr b.property)
  let C := B.restrictScalars k
  letI : Algebra.Smooth A B := Algebra.Smooth.of_isLocalization_Away (b : A)
  letI : Algebra.Smooth k B := Algebra.Smooth.comp k A B
  letI : Algebra.Smooth k C := by
    change Algebra.Smooth k B
    infer_instance
  refine ⟨C.map L.val,
    Algebra.Smooth.of_equiv (C.equivMapOfInjective L.val L.val.injective), ?_⟩
  intro x hx
  refine ⟨⟨x, IntermediateField.subset_adjoin k (E : Set K) hx⟩, ?_, rfl⟩
  obtain ⟨a, ha⟩ := hb ⟨x, hx⟩
  have hb0 : algebraMap A L (b : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  refine ⟨a, b, Submonoid.mem_powers (b : A), ?_⟩
  calc
    (⟨x, IntermediateField.subset_adjoin k (E : Set K) hx⟩ : L) =
        (⟨x, IntermediateField.subset_adjoin k (E : Set K) hx⟩ : L) *
          (algebraMap A L (b : A) * (algebraMap A L (b : A))⁻¹) := by
      rw [mul_inv_cancel₀ hb0, mul_one]
    _ = algebraMap A L a * (algebraMap A L (b : A))⁻¹ := by
      rw [← mul_assoc, mul_comm _ (algebraMap A L (b : A)), ← Algebra.smul_def, ← ha]

/-- Explicit-hypothesis form of `exists_smooth_subalgebra_containing_finset`; this avoids
installing a proposition-valued separability witness solely for the call. -/
@[stacks 07BV "explicit finite smooth-cover bridge"]
theorem exists_smooth_subalgebra_containing_finset_of
    (hsep : Algebra.IsSeparableOver k K) (E : Finset K) :
    ∃ A : Subalgebra k K, Algebra.Smooth k A ∧ (E : Set K) ⊆ A := by
  letI := hsep
  exact exists_smooth_subalgebra_containing_finset E

/-- A separable field extension is the directed supremum of a nonempty family
of smooth subalgebras. -/
@[stacks 07BV "directed smooth subalgebra family"]
theorem exists_directed_smooth_subalgebra_family [Algebra.IsSeparableOver k K] :
    ∃ (ι : Type (max u v)) (S : ι → Subalgebra k K), Nonempty ι ∧
      Directed (· ≤ ·) S ∧ (∀ i, Algebra.Smooth k (S i)) ∧
        iSup S = (⊤ : Subalgebra k K) := by
  classical
  let ι := ULift.{u} {A : Subalgebra k K // Algebra.Smooth k A}
  have hfg (i : ι) : i.down.1.FG := by
    letI := i.down.property
    exact i.down.1.fg_iff_finiteType.mpr inferInstance
  refine ⟨ι, fun i => i.down.1, ?_, ?_, fun i => i.down.property, ?_⟩
  · obtain ⟨A, hA, _⟩ := exists_smooth_subalgebra_containing_finset (k := k) (∅ : Finset K)
    exact ⟨⟨⟨A, hA⟩⟩⟩
  · intro i j
    obtain ⟨s, hs⟩ := hfg i
    obtain ⟨t, ht⟩ := hfg j
    obtain ⟨A, hA, hst⟩ := exists_smooth_subalgebra_containing_finset (k := k) (s ∪ t)
    refine ⟨⟨⟨A, hA⟩⟩, ?_, ?_⟩
    · change i.down.1 ≤ A
      rw [← hs]
      exact Algebra.adjoin_le fun x hx => hst (Finset.mem_union.mpr (Or.inl hx))
    · change j.down.1 ≤ A
      rw [← ht]
      exact Algebra.adjoin_le fun x hx => hst (Finset.mem_union.mpr (Or.inr hx))
  · apply top_unique
    intro x _
    obtain ⟨A, hA, hx⟩ := exists_smooth_subalgebra_containing_finset (k := k) {x}
    exact (le_iSup (fun i : ι => i.down.1) ⟨⟨A, hA⟩⟩)
      (hx (show x ∈ ({x} : Finset K) by simp))

/-- Explicit-hypothesis form of `exists_directed_smooth_subalgebra_family`; this keeps a
one-off separability proof out of local instance search. -/
@[stacks 07BV "explicit directed smooth-family bridge"]
theorem exists_directed_smooth_subalgebra_family_of
    (hsep : Algebra.IsSeparableOver k K) :
    ∃ (ι : Type (max u v)) (S : ι → Subalgebra k K), Nonempty ι ∧
      Directed (· ≤ ·) S ∧ (∀ i, Algebra.Smooth k (S i)) ∧
        iSup S = (⊤ : Subalgebra k K) := by
  letI := hsep
  exact exists_directed_smooth_subalgebra_family

end Algebra.IsSeparableOver
