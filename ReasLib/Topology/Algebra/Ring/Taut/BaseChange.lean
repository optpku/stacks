/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing

/-!
# Tautness under completed tensor base change

For continuous algebra maps `algebraMap A B` and `algebraMap A C` between linearly
topologized rings, tautness of the first implies tautness of `Completed.includeRight A B C`.
-/

@[expose] public section

universe u

open Algebra.TensorProduct

namespace RingHom

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
variable [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
variable [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
variable [Algebra A B] [Algebra A C]

/-- Let `algebraMap A B` and `algebraMap A C` be continuous
homomorphisms of linearly topologized rings. If `algebraMap A B` is taut, then
`Completed.includeRight A B C` is taut. -/
theorem IsTaut.completedTensor_includeRight
    (hB_cont : Continuous (algebraMap A B))
    (hC_cont : Continuous (algebraMap A C))
    (hB : (algebraMap A B).IsTaut) :
    (Completed.includeRight A B C).IsTaut := sorry

end RingHom
