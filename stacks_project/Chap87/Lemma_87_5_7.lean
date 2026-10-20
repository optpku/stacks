/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut
import StacksCheckRecall

/-!
# Lemma 87.5.7

A continuous taut homomorphism of linearly topologized rings transfers a
countable fundamental system of open ideals from the source to the target.
-/

@[expose] public section

universe u v

open scoped Topology

namespace RingHom.IsTaut

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/- Lemma 87.5.7: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` has a countable fundamental system of
open ideals, then `B` has a countable fundamental system of open ideals. -/
@[stacks 0GX6] #check (RingHom.IsTaut.isCountablyGenerated_nhds :
  ∀ {φ : A →+* B} (hcont : Continuous φ) (htaut : φ.IsTaut)
    [(nhds (0 : A)).IsCountablyGenerated],
    (nhds (0 : B)).IsCountablyGenerated)

end RingHom.IsTaut
