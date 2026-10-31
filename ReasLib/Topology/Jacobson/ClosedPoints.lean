/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Logic.Equiv.Set
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.Topology.LocallyClosed.FiniteUnion

/-!
# Closed-Point Traces in Jacobson Spaces

The closed-point subtype is Mathlib's canonical `closedPoints X`.  This leaf
adds the finite-locally-closed trace correspondence that it satisfies in a
Jacobson space.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IsOpenCover

/-- Lemma 5.18.4 (2): in a Jacobson space, the closed points are the union of
the closed points of the members of any open cover, viewed in the ambient space. -/
@[stacks 005W "closed points are the union of those in the cover members"]
theorem closedPoints_eq_iUnion_image {ι : Type*} {U : ι → Opens X} [JacobsonSpace X]
    (hU : IsOpenCover U) :
    closedPoints X = ⋃ i, Subtype.val '' closedPoints (U i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := hU.exists_mem x
    refine mem_iUnion.mpr ⟨i, ⟨⟨x, hi⟩, ?_, rfl⟩⟩
    exact preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val hx
  · intro hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    change y ∈ (Subtype.val : U i → X) ⁻¹' closedPoints X
    exact (congrArg (fun S : Set (U i) ↦ y ∈ S)
      (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints).mpr hy

end TopologicalSpace.IsOpenCover

namespace JacobsonSpace.ClosedPoints

variable [JacobsonSpace X]

private theorem subset_of_closedPointsTrace_subset
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E)
    (hE' : IsFiniteUnionOfLocallyClosed E')
    (htrace : (closedPoints X) ↓∩ E ⊆ (closedPoints X) ↓∩ E') : E ⊆ E' := by
  intro x hx
  by_contra hx'
  obtain ⟨n, S, hS, hdiff⟩ := (hE.sdiff hE').exists_eq_iUnion
  have hxS : x ∈ ⋃ i, S i := by
    rw [← hdiff]
    exact ⟨hx, hx'⟩
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxS
  obtain ⟨y, hyS, hyClosed⟩ := nonempty_inter_closedPoints ⟨x, hxi⟩ (hS i)
  have hyDiff : y ∈ E \ E' := by
    rw [hdiff]
    exact mem_iUnion.mpr ⟨i, hyS⟩
  exact hyDiff.2 (htrace (show (⟨y, hyClosed⟩ : closedPoints X) ∈
    (closedPoints X) ↓∩ E from hyDiff.1))

/-- Lemma 5.18.7 (1): taking the trace on `closedPoints X` is a bijection on
finite unions of locally closed subsets. -/
@[stacks 005Z "bijection on finite unions of locally closed subsets"]
theorem finiteUnionOfLocallyClosed_bijOn :
    Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F} := by
  refine ⟨?_, ?_, ?_⟩
  · intro E hE
    exact hE.preimage continuous_subtype_val
  · intro E hE E' hE' htrace
    exact (subset_of_closedPointsTrace_subset hE hE' htrace.subset).antisymm
      (subset_of_closedPointsTrace_subset hE' hE htrace.symm.subset)
  · intro F hF
    obtain ⟨n, S, hS, rfl⟩ := hF.exists_eq_iUnion
    have hlift : ∀ i, ∃ T : Set X, IsLocallyClosed T ∧ (closedPoints X) ↓∩ T = S i :=
      fun i ↦ IsInducing.subtypeVal.isLocallyClosed_iff.mp (hS i)
    choose T hT hTS using hlift
    refine ⟨⋃ i, T i, IsFiniteUnionOfLocallyClosed.iUnion_of_isLocallyClosed hT, ?_⟩
    simp only [preimage_iUnion, hTS]

/-- The closed-point trace equivalence induced by a supplied finite-locally-closed trace
bijection. The inverse is noncomputable; use `finiteUnionTraceEquiv_symm_apply_trace` rather
than inspecting its choice. Keeping the bijection proof as an argument ensures that this
non-Prop construction does not inherit statement-stage proof debt. -/
@[stacks 005Z "equivalence of finite-locally-closed closed-point traces"]
noncomputable def finiteUnionTraceEquiv
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F}) :
    {E : Set X // IsFiniteUnionOfLocallyClosed E} ≃
      {F : Set (closedPoints X) // IsFiniteUnionOfLocallyClosed F} :=
  h.equiv _

/-- `finiteUnionTraceEquiv` applies to a finite-locally-closed subset by
taking its canonical trace on `closedPoints X`. -/
@[simp]
theorem finiteUnionTraceEquiv_apply
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F})
    (E : {E : Set X // IsFiniteUnionOfLocallyClosed E}) :
    (finiteUnionTraceEquiv h E).val = (closedPoints X) ↓∩ E.val := by
  rfl

/-- Membership in the forward image under `finiteUnionTraceEquiv` is
membership of the underlying closed point in the ambient subset. -/
@[simp]
theorem mem_finiteUnionTraceEquiv_iff
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F})
    (E : {E : Set X // IsFiniteUnionOfLocallyClosed E}) {x : closedPoints X} :
    x ∈ (finiteUnionTraceEquiv h E).val ↔ x.val ∈ E.val := by
  rfl

/-- The chosen inverse of `finiteUnionTraceEquiv` is characterized by its
closed-point trace. -/
@[simp]
theorem finiteUnionTraceEquiv_symm_apply_trace
    (h : Set.BijOn (fun E : Set X ↦ (closedPoints X) ↓∩ E)
      {E : Set X | IsFiniteUnionOfLocallyClosed E}
      {F : Set (closedPoints X) | IsFiniteUnionOfLocallyClosed F})
    (F : {F : Set (closedPoints X) // IsFiniteUnionOfLocallyClosed F}) :
    (closedPoints X) ↓∩ ((finiteUnionTraceEquiv h).symm F).val = F.val := by
  exact congrArg Subtype.val ((finiteUnionTraceEquiv h).apply_symm_apply F)

end JacobsonSpace.ClosedPoints

namespace IsFiniteUnionOfLocallyClosed

variable [JacobsonSpace X]

/-- Lemma 5.18.7 (2): the closed-point trace reflects and preserves inclusion
between finite unions of locally closed subsets. -/
@[stacks 005Z "inclusion-preserving correspondence"]
theorem closedPointsTrace_subset_iff
    {E E' : Set X} (hE : IsFiniteUnionOfLocallyClosed E) (hE' : IsFiniteUnionOfLocallyClosed E') :
    (closedPoints X) ↓∩ E ⊆ (closedPoints X) ↓∩ E' ↔ E ⊆ E' := by
  constructor
  · exact JacobsonSpace.ClosedPoints.subset_of_closedPointsTrace_subset hE hE'
  · intro h x hx
    exact h hx

/-- Lemma 5.18.7 (3): within the finite-locally-closed trace correspondence,
local closedness is reflected and preserved. -/
@[stacks 005Z "preservation of locally closed subsets"]
theorem isLocallyClosed_iff_closedPointsTrace
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsLocallyClosed E ↔ IsLocallyClosed ((closedPoints X) ↓∩ E) := by
  constructor
  · intro h
    exact h.preimage continuous_subtype_val
  · intro h
    obtain ⟨E', hE', htrace⟩ := IsInducing.subtypeVal.isLocallyClosed_iff.mp h
    have heq : E' = E :=
      JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_bijOn.injOn
        hE'.isFiniteUnionOfLocallyClosed hE htrace
    rwa [heq] at hE'

/-- Lemma 5.18.7 (4): within the finite-locally-closed trace correspondence,
openness is reflected and preserved. -/
@[stacks 005Z "preservation of open subsets"]
theorem isOpen_iff_closedPointsTrace
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsOpen E ↔ IsOpen ((closedPoints X) ↓∩ E) := by
  constructor
  · intro h
    exact h.preimage continuous_subtype_val
  · intro h
    obtain ⟨E', hE', htrace⟩ := IsInducing.subtypeVal.isOpen_iff.mp h
    have heq : E' = E :=
      JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_bijOn.injOn
        hE'.isLocallyClosed.isFiniteUnionOfLocallyClosed hE htrace
    rwa [heq] at hE'

/-- Lemma 5.18.7 (5): within the finite-locally-closed trace correspondence,
closedness is reflected and preserved. -/
@[stacks 005Z "preservation of closed subsets"]
theorem isClosed_iff_closedPointsTrace
    {E : Set X} (hE : IsFiniteUnionOfLocallyClosed E) :
    IsClosed E ↔ IsClosed ((closedPoints X) ↓∩ E) := by
  constructor
  · intro h
    exact h.preimage continuous_subtype_val
  · intro h
    obtain ⟨E', hE', htrace⟩ := IsInducing.subtypeVal.isClosed_iff.mp h
    have heq : E' = E :=
      JacobsonSpace.ClosedPoints.finiteUnionOfLocallyClosed_bijOn.injOn
        hE'.isLocallyClosed.isFiniteUnionOfLocallyClosed hE htrace
    rwa [heq] at hE'

end IsFiniteUnionOfLocallyClosed
