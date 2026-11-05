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

/- Lemma 5.15.5: constructible subsets of retrocompact open subspaces are
constructible in the ambient space. -/
@[stacks 09YD]
#check fun {X : Type u} [TopologicalSpace X] {U : TopologicalSpace.Opens X} {E : Set U}
    (hE : Topology.IsConstructible E) (hU : IsRetrocompact (U : Set X)) ↦
  hE.image_of_isOpenEmbedding U.isOpen.isOpenEmbedding_subtypeVal
    (by simpa only [Subtype.range_coe] using hU)
