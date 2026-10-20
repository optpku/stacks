/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Weakly
public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing
public import Mathlib.Topology.Algebra.Algebra

/-!
# Weakly adic completed tensor products

If `algebraMap B A` and `algebraMap B C` are continuous maps of linearly
topologized rings and `A`, `C` are weakly pre-adic, then the completed tensor
`Completed B A C` is weakly adic.
-/

@[expose] public section

universe u

namespace Algebra.TensorProduct.Completed

variable {B A C : Type u}
variable [CommRing B] [CommRing A] [CommRing C]
variable [Algebra B A] [Algebra B C]
variable [TopologicalSpace B] [TopologicalSpace A] [TopologicalSpace C]

/-- The completed tensor product of weakly pre-adic algebras with continuous
structure maps over a linearly topologized ring is weakly adic. -/
theorem isWeaklyAdicRing [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsWeaklyPreadicRing A]
    [TopologicalRing.IsWeaklyPreadicRing C]
    (hA : Continuous (algebraMap B A)) (hC : Continuous (algebraMap B C)) :
    TopologicalRing.IsWeaklyAdicRing (Completed B A C) := sorry

/-- The completed tensor product of weakly pre-adic algebras with continuous
scalar multiplication over a linearly topologized ring is weakly adic. -/
instance instIsWeaklyAdicRing [IsTopologicalRing B] [IsLinearTopology B B]
    [TopologicalRing.IsWeaklyPreadicRing A]
    [TopologicalRing.IsWeaklyPreadicRing C]
    [ContinuousSMul B A] [ContinuousSMul B C] :
    TopologicalRing.IsWeaklyAdicRing (Completed B A C) :=
  isWeaklyAdicRing (continuous_algebraMap B A) (continuous_algebraMap B C)

end Algebra.TensorProduct.Completed
