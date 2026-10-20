/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.DirectLimit.Universal
public import ReasLib.RingTheory.DirectLimit.Algebra

@[expose] public section

universe u v w

/- Exercise 111.2.2 (1): the canonical maps into the direct limit respect every transition. -/
@[stacks 078J] #check (Ring.DirectLimit.Algebra.of_comp :
  ∀ {ι : Type u} [Preorder ι] {A : ι → Type v} [∀ i, CommRing (A i)]
    (φ : ∀ i j, i ≤ j → A i →+* A j) {i j : ι} (hij : i ≤ j),
    (Ring.DirectLimit.of A (φ · · ·) j).comp (φ i j hij) =
      Ring.DirectLimit.of A (φ · · ·) i)

/- Exercise 111.2.2 (2): every compatible family of ring maps factors uniquely through
the canonical maps into the direct limit of the directed system. -/
@[stacks 078J] #check (Ring.DirectLimit.existsUnique_hom :
  ∀ {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (A : ι → Type v) [∀ i, CommRing (A i)]
    (φ : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (φ · · ·)]
    {B : Type w} [CommRing B] (ψ : ∀ i, A i →+* B)
    (hψ : ∀ ⦃i j⦄ (hij : i ≤ j), (ψ j).comp (φ i j hij) = ψ i),
    ∃! Ψ : Ring.DirectLimit A (φ · · ·) →+* B,
      ∀ i, ψ i = Ψ.comp (Ring.DirectLimit.of A (φ · · ·) i))
