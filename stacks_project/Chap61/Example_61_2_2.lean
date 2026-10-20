/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Counterexamples.NotWLocal
import StacksCheckRecall

/-!
# Example 61.2.2

A profinite space `T` with a non-quasi-compact puncturing yields a space
whose closed points are the zero-slice `T × {0}`, which maps bijectively to
connected components, yet is not closed.
-/

@[expose] public section

open Set Topology

universe u

variable {T : Type u} [TopologicalSpace T]
  [CompactSpace T] [T2Space T] [TotallyDisconnectedSpace T]

/- Example 61.2.2 (5): the set of closed points is not closed, so Lemma 61.2.1
(1)–(2) do not force closedness of closed points. -/
@[stacks 0969] #check (Topology.NotWLocal.not_isClosed_closedPoints :
  ∀ (t : T), ¬ IsCompact ({t}ᶜ : Set T) →
    ¬ IsClosed (closedPoints (Topology.NotWLocal T t)))

/- Example 61.2.2 (1): the space `T × {0, 1}` with the source subbasis topology. -/
@[stacks 0969]
#check (Topology.NotWLocal :
  ∀ (T : Type u) [TopologicalSpace T], T → Type u)

/- Example 61.2.2 (2): the closed points of `NotWLocal T t` are the zero-slice
`T × {0}`. -/
@[stacks 0969]
#check (Topology.NotWLocal.closedPoints_eq :
  ∀ (t : T), ¬ IsCompact ({t}ᶜ : Set T) →
    closedPoints (Topology.NotWLocal T t) = Topology.NotWLocal.zeroSlice t)

/- Example 61.2.2 (3): the point `(t, 1)` lies in the closure of the zero-slice. -/
@[stacks 0969]
#check (Topology.NotWLocal.mem_closure_zeroSlice :
  ∀ (t : T), ¬ IsCompact ({t}ᶜ : Set T) →
    Topology.NotWLocal.mk t 1 ∈ closure (Topology.NotWLocal.zeroSlice t))

/- Example 61.2.2 (4): the canonical map from the zero-slice of closed points to
connected components is bijective. -/
@[stacks 0969]
#check (Topology.NotWLocal.bijective_fromClosedPoints :
  ∀ (t : T), ¬ IsCompact ({t}ᶜ : Set T) →
    Function.Bijective
      (ConnectedComponents.fromClosedPoints :
        closedPoints (Topology.NotWLocal T t) →
          ConnectedComponents (Topology.NotWLocal T t)))
