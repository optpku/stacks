/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Kernels of maps into completed quotients
-/

@[expose] public section

open TopologicalRing

noncomputable section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]

/-- The kernel of `A → (A ⧸ K)^∧` is the closure of `K`. -/
theorem ker_algebraMap_eq_closure (K : Ideal A) :
    RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) = K.closure := sorry

/-- The kernel of the canonical map into the completion of a closed quotient is the closed ideal. -/
theorem ker_algebraMap_quotient (K : Ideal A) [IsClosed (K : Set A)] :
    RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) = K := sorry

/-- Membership in the kernel of `A → (A ⧸ K)^∧` is membership in the closed
ideal `K`. -/
theorem mem_ker_algebraMap_quotient (K : Ideal A) [IsClosed (K : Set A)]
    {x : A} :
    x ∈ RingHom.ker (algebraMap A (weakIdealCompletion A (A ⧸ K))) ↔ x ∈ K := sorry

/-- There exists a weakly admissible topological ring with a closed ideal whose
canonical map into the completed quotient is not surjective. -/
theorem exists_not_surjective_algebraMap_quotient :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : IsWeaklyAdmissibleRing A) (K : Ideal A),
      IsClosed (K : Set A) ∧
        ¬ Function.Surjective (algebraMap A (weakIdealCompletion A (A ⧸ K))) := sorry

end TopologicalRing.weakIdealCompletion
