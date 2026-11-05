/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

universe u

open scoped Set.Notation

/- Lemma 5.15.7: constructible subsets restrict to closed subspaces with
compact complement. -/
@[stacks 09YE]
#check fun {X : Type u} [TopologicalSpace X] {Z E : Set X}
    (hE : Topology.IsConstructible E) (hZ : IsClosed Z) (hZc : IsCompact Zᶜ) ↦
  (hE.preimage_of_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal
    (by simpa only [Subtype.range_coe] using hZc) : Topology.IsConstructible (Z ↓∩ E))
