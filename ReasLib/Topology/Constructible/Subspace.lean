/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Constructible.Retrocompact

/-!
# Constructible Sets in Subspaces

The canonical subtype inclusion is used directly, with bridges for
retrocompact and constructible subspaces that Mathlib does not package.
The open and closed subtype lemmas below are untagged adapters to Mathlib's
embedding lemmas: they expose the trace notation `U ↓∩ E` and accept hypotheses
on the subset itself instead of on `Set.range Subtype.val`.
-/

@[expose] public section

universe u

open Set TopologicalSpace
open scoped Set.Notation

namespace Topology

/-- Lemma 5.15.4: a constructible subset has constructible trace on an open
subspace. This trace-notation adapter specializes
`IsConstructible.preimage_of_isOpenEmbedding`, the canonical owner of tag 005J. -/
theorem IsConstructible.preimage_subtypeVal_of_isOpen
    {X : Type u} [TopologicalSpace X] {U E : Set X}
    (hE : IsConstructible E) (hU : IsOpen U) :
    IsConstructible (U ↓∩ E) :=
  hE.preimage_of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal

/-- Lemma 5.15.5: a constructible subset of a retrocompact open subspace has
constructible image in the ambient space. This bundled-open adapter specializes
`IsConstructible.image_of_isOpenEmbedding`, the canonical owner of tag 09YD. -/
theorem IsConstructible.image_subtypeVal_of_isRetrocompact
    {X : Type u} [TopologicalSpace X] {U : Opens X} {E : Set U}
    (hE : IsConstructible E) (hU : IsRetrocompact (U : Set X)) :
    IsConstructible (Subtype.val '' E : Set X) :=
  hE.image_of_isOpenEmbedding U.isOpen.isOpenEmbedding_subtypeVal
    (by simpa using hU)

/-- Lemma 5.15.7: a constructible subset has constructible trace on a closed
subspace with compact complement. This trace-notation adapter specializes
`IsConstructible.preimage_of_isClosedEmbedding`, the canonical owner of tag 09YE. -/
theorem IsConstructible.preimage_subtypeVal_of_isClosed_of_isCompact_compl
    {X : Type u} [TopologicalSpace X] {Z E : Set X} (hE : IsConstructible E)
    (hZ : IsClosed Z) (hZc : IsCompact Zᶜ) : IsConstructible (Z ↓∩ E) :=
  hE.preimage_of_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal
    (by simpa using hZc)

/-- Lemma 5.15.9: a constructible subset of a closed subspace with
retrocompact complement has constructible ambient image. This bundled-closed adapter specializes
`IsConstructible.image_of_isClosedEmbedding`, the canonical owner of tag 09YG. -/
theorem IsConstructible.image_subtypeVal_of_isRetrocompact_compl
    {X : Type u} [TopologicalSpace X] {Z : Closeds X} {E : Set Z}
    (hE : IsConstructible E) (hZc : IsRetrocompact ((Z : Set X)ᶜ)) :
    IsConstructible (Subtype.val '' E : Set X) :=
  hE.image_of_isClosedEmbedding Z.isClosed.isClosedEmbedding_subtypeVal
    (by simpa using hZc)

variable {X : Type u} [TopologicalSpace X] [PrespectralSpace X]
variable {T E : Set X}

/-- Lemma 5.15.8: constructible subsets pull back to a retrocompact subspace
of a prespectral space. -/
@[stacks 09YF]
theorem IsConstructible.preimage_subtypeVal_of_isRetrocompact
    (hE : IsConstructible E) (hT : IsRetrocompact T) :
    IsConstructible (T ↓∩ E) := sorry

/-- Lemma 5.15.11: constructible subsets pull back to constructible subspaces
of a prespectral space. -/
@[stacks 09YI]
theorem IsConstructible.preimage_subtypeVal_of_isConstructible
    (hE : IsConstructible E) (hT : IsConstructible T) :
    IsConstructible (T ↓∩ E) := sorry

/-- Lemma 5.15.12: a constructible subset of a constructible subspace of a
prespectral space has constructible ambient image. -/
@[stacks 09YJ]
theorem IsConstructible.image_subtypeVal_of_isConstructible
    {E : Set X} {F : Set E} (hF : IsConstructible F) (hE : IsConstructible E) :
    IsConstructible (Subtype.val '' F : Set X) := sorry

end Topology
