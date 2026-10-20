/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut
import StacksCheckRecall

@[expose] public section

universe u v

variable {A : Type u} {B : Type v}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]

/- Definition 87.5.1: a continuous homomorphism `φ : A →+* B` of linearly
topologized rings is taut if for every open ideal `I` of `A` the closure of
`Ideal.map φ I` is open in `B` and these closures form a fundamental system of
open ideals of `B`. -/
@[stacks 0AMX] #check (RingHom.IsTaut : (A →+* B) → Prop)
