/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.FaithfullyFlatOpenQuotients

/-!
# Faithfully flat open quotients of taut ring maps

In the standing situation of Stacks section 87.8, a continuous taut homomorphism
`φ : A →+* B` of linearly topologized rings is assumed to induce a faithfully
flat map `A ⧸ I →+* B ⧸ J` for every open ideal `I` of `A`, where `J` is the
closure of `Ideal.map φ I`.
-/

@[expose] public section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

#check (RingHom.FaithfullyFlatOpenQuotients : (A →+* B) → Prop)
