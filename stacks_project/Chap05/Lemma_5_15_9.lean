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

/- Lemma 5.15.9: constructible subsets of closed subspaces with retrocompact
complement have constructible ambient image. -/
@[stacks 09YG "constructible subsets of closed subspaces"]
#check fun {X : Type u} [TopologicalSpace X] {Z : TopologicalSpace.Closeds X} {E : Set Z}
    (hE : Topology.IsConstructible E) (hZc : IsRetrocompact ((Z : Set X)ᶜ)) ↦
  hE.image_of_isClosedEmbedding Z.isClosed.isClosedEmbedding_subtypeVal
    (by simpa only [Subtype.range_coe] using hZc)
