/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.TensorProduct.WeaklyAdic
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 87.7.6: If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are weakly pre-adic, then
A ⊗̂_B C is weakly adic. -/
@[stacks 0GXJ] #check (Algebra.TensorProduct.Completed.isWeaklyAdicRing :
  ∀ {B A C : Type u} [CommRing B] [CommRing A] [CommRing C]
    [Algebra B A] [Algebra B C]
    [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]
    [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsWeaklyPreadicRing A]
    [TopologicalRing.IsWeaklyPreadicRing C],
    Continuous (algebraMap B A) → Continuous (algebraMap B C) →
    TopologicalRing.IsWeaklyAdicRing (Algebra.TensorProduct.Completed B A C))
