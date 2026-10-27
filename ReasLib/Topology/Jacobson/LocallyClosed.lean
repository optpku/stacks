/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.LocallyClosed.LocalUnion

/-!
# Jacobson Subspaces from Locally Closed Unions

Jacobson-space inheritance is stated on the locally union-of-locally-closed
predicate. Constructible specializations live in a separate leaf.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

namespace IsLocallyUnionOfLocallyClosed

private theorem nonempty_inter_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyUnionOfLocallyClosed T) {Z : Set T} (hZ : Z.Nonempty)
    (hZ' : IsLocallyClosed Z) : (Z ∩ (T ↓∩ closedPoints X)).Nonempty := by
  obtain ⟨x, hx⟩ := hZ
  obtain ⟨U, hUx, hU, S, hS, hUS⟩ := hT (x : X)
  have hxU : (x : X) ∈ U := mem_of_mem_nhds hUx
  have hxS : (⟨(x : X), hxU⟩ : U) ∈ ⋃₀ S := by
    rw [← hUS]
    exact x.property
  obtain ⟨C, hCS, hxC⟩ := mem_sUnion.mp hxS
  obtain ⟨A, hA, hAZ⟩ :=
    (IsInducing.subtypeVal : IsInducing (Subtype.val : T → X)).isLocallyClosed_iff.mp hZ'
  have hxA : (x : X) ∈ A := by
    change x ∈ T ↓∩ A
    rw [hAZ]
    exact hx
  have hC : IsLocallyClosed ((Subtype.val : U → X) '' C) :=
    (hS C hCS).image IsInducing.subtypeVal
      hU.isOpenEmbedding_subtypeVal.isOpen_range.isLocallyClosed
  obtain ⟨y, hy, hyClosed⟩ := nonempty_inter_closedPoints
    (Z := A ∩ ((Subtype.val : U → X) '' C))
    ⟨(x : X), hxA, ⟨⟨(x : X), hxU⟩, hxC, rfl⟩⟩ (hA.inter hC)
  obtain ⟨y, hyC, rfl⟩ := hy.2
  have hyT : (y : X) ∈ T := by
    change y ∈ U ↓∩ T
    rw [hUS]
    exact mem_sUnion_of_mem hyC hCS
  refine ⟨⟨(y : X), hyT⟩, ?_, hyClosed⟩
  rw [← hAZ]
  exact hy.1

/-- Lemma 5.18.5 (1): a locally union-of-locally-closed subspace of a
Jacobson space is Jacobson. -/
@[stacks 005X "Jacobson subspaces from locally closed unions"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyUnionOfLocallyClosed T) : JacobsonSpace T := by
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  obtain ⟨x, hx, hxClosed⟩ := nonempty_inter_preimage_closedPoints hT hZ hZ'
  exact ⟨x, hx,
    preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val hxClosed⟩

/-- Lemma 5.18.5 (2): closed points of a locally union-of-locally-closed
subspace of a Jacobson space remain closed in the ambient space. -/
@[stacks 005X "closed points remain closed in the ambient Jacobson space"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyUnionOfLocallyClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  obtain ⟨y, rfl, hy⟩ := nonempty_inter_preimage_closedPoints hT (singleton_nonempty x)
    (mem_closedPoints_iff.mp hx).isLocallyClosed
  exact hy

end IsLocallyUnionOfLocallyClosed

namespace IsUnionOfLocallyClosed

private theorem locallyUnionOfLocallyClosed {T : Set X} (hT : IsUnionOfLocallyClosed T) :
    IsLocallyUnionOfLocallyClosed T := by
  intro x
  refine ⟨univ, Filter.univ_mem, isOpen_univ, ?_⟩
  obtain ⟨S, hS, hTS⟩ := hT
  refine ⟨(fun Z : Set X ↦ (univ : Set X) ↓∩ Z) '' S, ?_, ?_⟩
  · rintro _ ⟨Z, hZS, rfl⟩
    exact (hS Z hZS).preimage continuous_subtype_val
  · rw [hTS, preimage_sUnion, sUnion_image]

/-- Lemma 5.18.5 (4): a union of locally closed subspaces of a Jacobson space is Jacobson. -/
@[stacks 005X "(4) unions of locally closed subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsUnionOfLocallyClosed T) : JacobsonSpace T := by
  exact (locallyUnionOfLocallyClosed hT).jacobsonSpace_subtype

/-- Lemma 5.18.5 (4): closed points of a union of locally closed subspaces are ambiently closed. -/
@[stacks 005X "(4) closed points of unions of locally closed subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsUnionOfLocallyClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  exact (locallyUnionOfLocallyClosed hT).closedPoints_subset_preimage_closedPoints

end IsUnionOfLocallyClosed

namespace IsOpen

/- The first four source cases are exposed as direct methods so callers do not
have to manually pass through the weakest locally-union predicate. -/

/-- Lemma 5.18.5 (1): an open subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(1) open subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsOpen T) : JacobsonSpace T := by
  exact JacobsonSpace.of_isOpenEmbedding hT.isOpenEmbedding_subtypeVal

/-- Lemma 5.18.5 (1): closed points of an open subspace are ambiently closed. -/
@[stacks 005X "(1) closed points of open subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsOpen T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  change x ∈ (Subtype.val : T → X) ⁻¹' closedPoints X
  rwa [hT.isOpenEmbedding_subtypeVal.preimage_closedPoints]

end IsOpen

namespace IsClosed

/-- Lemma 5.18.5 (2): a closed subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(2) closed subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsClosed T) : JacobsonSpace T := by
  exact JacobsonSpace.of_isClosedEmbedding hT.isClosedEmbedding_subtypeVal

/-- Lemma 5.18.5 (2): closed points of a closed subspace are ambiently closed. -/
@[stacks 005X "(2) closed points of closed subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  change x ∈ (Subtype.val : T → X) ⁻¹' closedPoints X
  rwa [hT.isClosedEmbedding_subtypeVal.preimage_closedPoints]

end IsClosed

namespace IsLocallyClosed

/-- Lemma 5.18.5 (3): a locally closed subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(3) locally closed subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyClosed T) : JacobsonSpace T := by
  rw [jacobsonSpace_iff_locallyClosed]
  intro Z hZ hZ'
  obtain ⟨_, ⟨x, hx, rfl⟩, hxClosed⟩ := nonempty_inter_closedPoints
    (hZ.image (Subtype.val : T → X)) (hZ'.image IsInducing.subtypeVal (by simpa using hT))
  exact ⟨x, hx,
    preimage_closedPoints_subset Subtype.val_injective continuous_subtype_val hxClosed⟩

/-- Lemma 5.18.5 (3): closed points of a locally closed subspace are ambiently closed. -/
@[stacks 005X "(3) closed points of locally closed subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := by
  intro x hx
  apply isClosed_singleton_of_isLocallyClosed_singleton
  rw [← image_singleton]
  exact (mem_closedPoints_iff.mp hx).isLocallyClosed.image IsInducing.subtypeVal
    (by simpa using hT)

end IsLocallyClosed
