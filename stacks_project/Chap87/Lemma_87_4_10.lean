/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.TopologicalNilradical
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 87.4.10 (1): the set of topologically nilpotent elements of a
linearly topologized ring is a closed ideal. -/
@[stacks 0AMW] #check (topologicalNilradical.isClosed :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], IsClosed (topologicalNilradical R : Set R))

/- Lemma 87.4.10 (2): the set of topologically nilpotent elements of a
linearly topologized ring is a radical ideal. -/
@[stacks 0AMW] #check (@topologicalNilradical.isRadical :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], (topologicalNilradical R).IsRadical)

/- Lemma 87.4.10 (3): a continuous map of linearly topologized rings sends
topologically nilpotent elements to topologically nilpotent elements. -/
@[stacks 0AMW] #check (topologicalNilradical.map_isTopologicallyNilpotent :
  ∀ {R : Type u} {S : Type v} [TopologicalSpace R] [MonoidWithZero R]
    [MonoidWithZero S] [TopologicalSpace S] {F : Type w} [FunLike F R S]
    [MonoidWithZeroHomClass F R S] {φ : F}, Continuous φ → ∀ {a : R},
    IsTopologicallyNilpotent a → IsTopologicallyNilpotent (φ a))

/- Lemma 87.4.10 (4): if a subset of the source consists of topologically
nilpotent elements, then the closure of the extended image ideal consists of
topologically nilpotent elements. -/
@[stacks 0AMW] #check (topologicalNilradical.closure_span_image_le :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    (φ : A →+* B), Continuous φ → ∀ {s : Set A},
    s ⊆ topologicalNilradical A →
    (Ideal.span (φ '' s)).closure ≤ topologicalNilradical B)
