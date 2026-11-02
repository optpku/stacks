/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Jacobson.ClosedPoints

/-!
# Constructible Closed-Point Traces

Constructible subsets of a Jacobson space are recovered from their traces on
the canonical subtype of closed points.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

namespace JacobsonSpace.ClosedPoints

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

omit [JacobsonSpace X] in
private theorem finiteUnionOfLocallyClosed_of_constructible {E : Set X}
    (hE : IsConstructible E) : IsFiniteUnionOfLocallyClosed E := by
  induction hE using IsConstructible.empty_union_induction with
  | open_retrocompact U hUopen _ =>
    exact hUopen.isLocallyClosed.isFiniteUnionOfLocallyClosed
  | union _ _ _ _ ihS ihT => exact ihS.union ihT
  | compl _ _ ih => exact ih.compl

private theorem finiteUnion_subset_of_closedPointsTrace_subset
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hE' : IsFiniteUnionOfLocallyClosed E')
    (htrace : (closedPoints X) ↓∩ E ⊆ (closedPoints X) ↓∩ E') : E ⊆ E' := by
  intro x hx
  by_contra hx'
  obtain ⟨S, _, hS, hdiff⟩ := hE.sdiff hE'
  have hxS : x ∈ ⋃₀ S := by
    rw [← hdiff]
    exact ⟨hx, hx'⟩
  obtain ⟨Z, hZS, hxZ⟩ := mem_sUnion.mp hxS
  obtain ⟨y, hyZ, hyClosed⟩ := nonempty_inter_closedPoints ⟨x, hxZ⟩ (hS Z hZS)
  have hyDiff : y ∈ E \ E' := by
    rw [hdiff]
    exact mem_sUnion_of_mem hyZ hZS
  exact hyDiff.2 (htrace (show (⟨y, hyClosed⟩ : closedPoints X) ∈
    (closedPoints X) ↓∩ E from hyDiff.1))

private theorem isCompact_closedPointsTrace_iff {U : Set X} (hU : IsOpen U) :
    IsCompact ((closedPoints X) ↓∩ U) ↔ IsCompact U := by
  constructor
  · intro h
    apply isCompact_of_finite_subcover
    intro ι V hV hUV
    have hcover : (closedPoints X) ↓∩ U ⊆ ⋃ i, (closedPoints X) ↓∩ V i := by
      simpa only [preimage_iUnion] using
        preimage_mono (f := (Subtype.val : closedPoints X → X)) hUV
    obtain ⟨t, ht⟩ := h.elim_finite_subcover (fun i ↦ (closedPoints X) ↓∩ V i)
      (fun i ↦ (hV i).preimage continuous_subtype_val) hcover
    refine ⟨t, finiteUnion_subset_of_closedPointsTrace_subset
      hU.isLocallyClosed.isFiniteUnionOfLocallyClosed
      (isOpen_biUnion fun i _ ↦ hV i).isLocallyClosed.isFiniteUnionOfLocallyClosed ?_⟩
    simpa only [preimage_iUnion, Finset.mem_coe] using ht
  · intro h
    apply isCompact_of_finite_subcover
    intro ι V hV hUV
    have hlift : ∀ i, ∃ W : Set X, IsOpen W ∧ (closedPoints X) ↓∩ W = V i :=
      fun i ↦ IsInducing.subtypeVal.isOpen_iff.mp (hV i)
    choose W hW hWV using hlift
    have hcover : U ⊆ ⋃ i, W i := by
      apply finiteUnion_subset_of_closedPointsTrace_subset
        hU.isLocallyClosed.isFiniteUnionOfLocallyClosed
        (isOpen_iUnion hW).isLocallyClosed.isFiniteUnionOfLocallyClosed
      simpa only [preimage_iUnion, hWV] using hUV
    obtain ⟨t, ht⟩ := h.elim_finite_subcover W hW hcover
    refine ⟨t, ?_⟩
    simpa only [preimage_iUnion, hWV] using
      preimage_mono (f := (Subtype.val : closedPoints X → X)) ht

private theorem isRetrocompact_open_closedPointsTrace_iff {U : Set X} (hU : IsOpen U) :
    IsRetrocompact U ↔ IsRetrocompact ((closedPoints X) ↓∩ U) := by
  constructor
  · intro h V hVcompact hVopen
    obtain ⟨W, hW, rfl⟩ := IsInducing.subtypeVal.isOpen_iff.mp hVopen
    exact (isCompact_closedPointsTrace_iff (hU.inter hW)).mpr
      (h ((isCompact_closedPointsTrace_iff hW).mp hVcompact) hW)
  · intro h W hWcompact hWopen
    exact (isCompact_closedPointsTrace_iff (hU.inter hWopen)).mp
      (h ((isCompact_closedPointsTrace_iff hWopen).mpr hWcompact)
        (hWopen.preimage continuous_subtype_val))

/-- Lemma 5.18.8 (1): taking the trace on `closedPoints X` is a bijection on
constructible subsets. -/
@[stacks 005Y "constructible closed-point trace correspondence"]
theorem constructible_bijOn :
    Set.BijOn
      (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F} := by
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    exact hE.preimage continuous_subtype_val fun U hU hUretro ↦
      (isRetrocompact_open_closedPointsTrace_iff hU).mp hUretro
  · intro E hE E' hE' htrace
    exact (finiteUnion_subset_of_closedPointsTrace_subset
      (finiteUnionOfLocallyClosed_of_constructible hE)
      (finiteUnionOfLocallyClosed_of_constructible hE') htrace.subset).antisymm
        (finiteUnion_subset_of_closedPointsTrace_subset
          (finiteUnionOfLocallyClosed_of_constructible hE')
          (finiteUnionOfLocallyClosed_of_constructible hE) htrace.symm.subset)
  · intro F hF
    induction hF using IsConstructible.empty_union_induction with
    | open_retrocompact V hVopen hVretro =>
      obtain ⟨U, hU, rfl⟩ := IsInducing.subtypeVal.isOpen_iff.mp hVopen
      exact ⟨U, ((isRetrocompact_open_closedPointsTrace_iff hU).mpr hVretro).isConstructible
        hU, rfl⟩
    | union S _ T _ ihS ihT =>
      obtain ⟨S', hS', hS'trace⟩ := ihS
      obtain ⟨T', hT', hT'trace⟩ := ihT
      refine ⟨S' ∪ T', hS'.union hT', ?_⟩
      change (closedPoints X) ↓∩ (S' ∪ T') = S ∪ T
      rw [preimage_union]
      exact congrArg₂ (· ∪ ·) hS'trace hT'trace
    | compl S _ ih =>
      obtain ⟨S', hS', htrace⟩ := ih
      refine ⟨S'ᶜ, hS'.compl, ?_⟩
      change (closedPoints X) ↓∩ S'ᶜ = Sᶜ
      rw [preimage_compl]
      exact congrArg (fun A : Set (closedPoints X) ↦ Aᶜ) htrace

/-- The closed-point trace equivalence induced by a supplied constructible trace bijection. The
inverse is noncomputable; use `constructibleTraceEquiv_symm_apply_trace` rather than inspecting
its choice. Keeping the bijection proof as an argument ensures that this non-Prop construction
does not inherit statement-stage proof debt. -/
@[stacks 005Y "equivalence of constructible closed-point traces"]
noncomputable def constructibleTraceEquiv
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F}) :
    {E : Set X // IsConstructible E} ≃
      {F : Set (closedPoints X) // IsConstructible F} :=
  h.equiv _

/-- `constructibleTraceEquiv` applies to a constructible subset by taking its
canonical trace on `closedPoints X`. -/
@[simp]
theorem constructibleTraceEquiv_apply
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F})
    (E : {E : Set X // IsConstructible E}) :
    (constructibleTraceEquiv h E).val = (closedPoints X) ↓∩ E.val := by
  rfl

/-- Membership in the forward image under `constructibleTraceEquiv` is
membership of the underlying closed point in the ambient subset. -/
@[simp]
theorem mem_constructibleTraceEquiv_iff
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F})
    (E : {E : Set X // IsConstructible E}) {x : closedPoints X} :
    x ∈ (constructibleTraceEquiv h E).val ↔ x.val ∈ E.val := by
  rfl

/-- The chosen inverse of `constructibleTraceEquiv` is characterized by its
closed-point trace. -/
@[simp]
theorem constructibleTraceEquiv_symm_apply_trace
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsConstructible E}
      {F : Set (closedPoints X) | IsConstructible F})
    (F : {F : Set (closedPoints X) // IsConstructible F}) :
    (closedPoints X) ↓∩ ((constructibleTraceEquiv h).symm F).val = F.val := by
  exact congrArg Subtype.val ((constructibleTraceEquiv h).apply_symm_apply F)

end JacobsonSpace.ClosedPoints

namespace Topology.IsConstructible

variable {X : Type u} [TopologicalSpace X] [JacobsonSpace X]

/-- Constructible closed-point traces reflect and preserve inclusion. -/
theorem closedPointsTrace_subset_iff
    {E E' : Set X} (hE : IsConstructible E) (hE' : IsConstructible E') :
    (closedPoints X) ↓∩ E ⊆ (closedPoints X) ↓∩ E' ↔ E ⊆ E' := by
  constructor
  · exact JacobsonSpace.ClosedPoints.finiteUnion_subset_of_closedPointsTrace_subset
      (JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_of_constructible hE)
      (JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_of_constructible hE')
  · intro h
    exact preimage_mono h

/-- A constructible subset has constructible trace on the closed-point subtype. -/
theorem closedPointsTrace {E : Set X} (hE : IsConstructible E) :
    IsConstructible ((closedPoints X) ↓∩ E) := by
  exact JacobsonSpace.ClosedPoints.constructible_bijOn.mapsTo hE

/-- Lemma 5.18.8 (2): for a constructible subset, being open and retrocompact
is reflected and preserved by its closed-point trace. -/
@[stacks 005Y "preservation of open retrocompact subsets"]
theorem isOpen_and_isRetrocompact_iff_closedPointsTrace
    {E : Set X} (hE : IsConstructible E) :
    IsOpen E ∧ IsRetrocompact E ↔
      IsOpen ((closedPoints X) ↓∩ E) ∧ IsRetrocompact ((closedPoints X) ↓∩ E) := by
  constructor
  · rintro ⟨hOpen, hRetro⟩
    exact ⟨hOpen.preimage continuous_subtype_val,
      (JacobsonSpace.ClosedPoints.isRetrocompact_open_closedPointsTrace_iff hOpen).mp hRetro⟩
  · rintro ⟨hOpen, hRetro⟩
    obtain ⟨U, hU, hUE⟩ := IsInducing.subtypeVal.isOpen_iff.mp hOpen
    have hEfinite := JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_of_constructible hE
    have hUfinite := hU.isLocallyClosed.isFiniteUnionOfLocallyClosed
    have heq : U = E :=
      (JacobsonSpace.ClosedPoints.finiteUnion_subset_of_closedPointsTrace_subset
        hUfinite hEfinite hUE.subset).antisymm
          (JacobsonSpace.ClosedPoints.finiteUnion_subset_of_closedPointsTrace_subset
            hEfinite hUfinite hUE.symm.subset)
    have hEopen : IsOpen E := heq ▸ hU
    exact ⟨hEopen,
      (JacobsonSpace.ClosedPoints.isRetrocompact_open_closedPointsTrace_iff hEopen).mpr hRetro⟩

/-- Lemma 5.18.8 (3): for a constructible subset, being the complement of an
open retrocompact subset is reflected and preserved by its closed-point trace. -/
@[stacks 005Y "preservation of complements of open retrocompact subsets"]
theorem isOpen_compl_and_isRetrocompact_compl_iff_closedPointsTrace
    {E : Set X} (hE : IsConstructible E) :
    IsOpen Eᶜ ∧ IsRetrocompact Eᶜ ↔
      IsOpen ((closedPoints X) ↓∩ E)ᶜ ∧ IsRetrocompact ((closedPoints X) ↓∩ E)ᶜ := by
  simpa only [preimage_compl] using hE.compl.isOpen_and_isRetrocompact_iff_closedPointsTrace

end Topology.IsConstructible
