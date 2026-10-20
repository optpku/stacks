/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.Adic.Weakly.Taut

@[expose] public section

universe u v

/- Lemma 87.7.5: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` is weakly pre-adic, then `B` is
weakly pre-adic. -/
@[stacks 0GXI] #check
  (TopologicalRing.IsWeaklyPreadicRing.of_isTaut :
    ∀ {A : Type u} {B : Type v}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyPreadicRing A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      {φ : A →+* B}, Continuous φ → φ.IsTaut →
        TopologicalRing.IsWeaklyPreadicRing B)
