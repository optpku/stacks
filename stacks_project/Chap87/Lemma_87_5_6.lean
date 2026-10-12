/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Lemma_87_5_6_CompletedRing

/-!
# Lemma 87.5.6

If `algebraMap A B` is a taut homomorphism of linearly topologized rings and
`algebraMap A C` is continuous, then `Completed.includeRight A B C` is taut.
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

/-- Lemma 87.5.6: Let `algebraMap A B` and `algebraMap A C` be continuous
homomorphisms of linearly topologized rings. If `algebraMap A B` is taut, then
`Completed.includeRight A B C` is taut. -/
@[stacks 0GX5]
theorem IsTaut.completedTensor_includeRight
    (hB_cont : Continuous (algebraMap A B))
    (hC_cont : Continuous (algebraMap A C))
    (hB : (algebraMap A B).IsTaut) :
    (Completed.includeRight A B C).IsTaut := sorry

end RingHom
