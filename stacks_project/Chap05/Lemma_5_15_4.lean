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

/- Lemma 5.15.4: a constructible subset has constructible trace on an open
subspace. -/
@[stacks 005J "constructible traces on open subspaces"]
#check fun {X : Type u} [TopologicalSpace X] {U E : Set X}
    (hE : Topology.IsConstructible E) (hU : IsOpen U) ↦
  (hE.preimage_of_isOpenEmbedding hU.isOpenEmbedding_subtypeVal :
    Topology.IsConstructible (U ↓∩ E))
