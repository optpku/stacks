module

public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Closed extended ideals and completed tensor products

The closure of an extended ideal is the kernel of the canonical map to the
completed tensor product with the quotient by that ideal.
-/

@[expose] public section

universe u

open Algebra.TensorProduct

namespace Ideal

variable {A B : Type u}
variable [CommRing A] [CommRing B]
variable [TopologicalSpace A] [TopologicalSpace B]
variable [IsTopologicalRing A] [IsTopologicalRing B]
variable [IsLinearTopology A A] [IsLinearTopology B B]
variable [Algebra A B]

/-- For a continuous map of linearly topologized rings, the closure of the extended
ideal is the kernel of the canonical map to the completed tensor product with the
quotient by the ideal. -/
theorem closure_map_eq_ker_includeLeft (hφ : Continuous (algebraMap A B)) (I : Ideal A) :
    (I.map (algebraMap A B)).closure = RingHom.ker (Completed.includeLeft A B (A ⧸ I)) := sorry

/-- Membership in the closure of an extended ideal is equivalent to vanishing
under the canonical map to the completed tensor product with the quotient. -/
theorem mem_closure_map_iff_includeLeft_eq_zero (hφ : Continuous (algebraMap A B))
    (I : Ideal A) {b : B} :
    b ∈ (I.map (algebraMap A B)).closure ↔
      Completed.includeLeft A B (A ⧸ I) b = 0 := sorry

end Ideal
