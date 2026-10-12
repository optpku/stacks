/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Ring.Ideal
public import stacks_project.Chap87.Lemma_87_5_6_CompletedRing

/-!
# Lemma 87.4.11

The topological closure of an extended ideal `IB` is the kernel of the canonical
map from `B` into the completed tensor product of `B` with `A ⧸ I` over `A`.
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

/-- Lemma 87.4.11: If `algebraMap A B` is a continuous map of linearly topologized rings
and `I` is an ideal of `A`, then the topological closure of `I.map (algebraMap A B)`
equals the kernel of `Completed.includeLeft A B (A ⧸ I)`. -/
@[stacks 0AMZ]
theorem closure_map_eq_ker_includeLeft (hφ : Continuous (algebraMap A B)) (I : Ideal A) :
    (I.map (algebraMap A B)).closure = RingHom.ker (Completed.includeLeft A B (A ⧸ I)) := sorry

/-- Membership in the topological closure of the extended ideal `I.map (algebraMap A B)`
is equivalent to vanishing under `Completed.includeLeft A B (A ⧸ I)`. -/
theorem mem_closure_map_iff_includeLeft_eq_zero (hφ : Continuous (algebraMap A B))
    (I : Ideal A) {b : B} :
    b ∈ (I.map (algebraMap A B)).closure ↔
      Completed.includeLeft A B (A ⧸ I) b = 0 := sorry

end Ideal
