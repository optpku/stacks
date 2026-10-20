/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Descent
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 87.8.3: In the situation above, if `B` is pre-admissible, then `A` is
pre-admissible. The situation is a continuous taut homomorphism `φ : A →+* B` of
linearly topologized rings such that `φ.FaithfullyFlatOpenQuotients`: for every
open ideal `I` of `A`, writing `J` for the closure of `Ideal.map φ I`, the induced
map `A ⧸ I →+* B ⧸ J` is faithfully flat. -/
@[stacks 0GXN] #check (TopologicalRing.IsPreadmissibleRing.of_isTaut :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsPreadmissibleRing B]
    {φ : A →+* B}, Continuous φ → φ.IsTaut → φ.FaithfullyFlatOpenQuotients →
      TopologicalRing.IsPreadmissibleRing A)
