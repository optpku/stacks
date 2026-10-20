/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly.Descent
import StacksCheckRecall

/-!
# Lemma 87.8.4

Weakly pre-adic rings descend along a continuous taut homomorphism of linearly
topologized rings with faithfully flat open quotients.
-/

@[expose] public section

universe u v

/- Lemma 87.8.4: In the situation above, if `B` is weakly pre-adic, then `A` is
weakly pre-adic. The situation is a continuous taut homomorphism `φ : A →+* B` of
linearly topologized rings such that `φ.FaithfullyFlatOpenQuotients`: for every
open ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`, the induced
map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
@[stacks 0GXP] #check (TopologicalRing.IsWeaklyPreadicRing.of_faithfullyFlatOpenQuotients :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyPreadicRing B]
    {φ : A →+* B}, Continuous φ → φ.IsTaut → φ.FaithfullyFlatOpenQuotients →
      TopologicalRing.IsWeaklyPreadicRing A)
