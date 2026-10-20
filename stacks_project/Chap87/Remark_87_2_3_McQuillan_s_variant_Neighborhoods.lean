/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealBasis

@[expose] public section

universe u

/- Weak ideals of definition form a neighbourhood basis in a weakly pre-admissible ring. -/
#check (TopologicalRing.hasBasis_isWeakIdealOfDefinition :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyPreadmissibleRing A],
    (nhds (0 : A)).HasBasis
      (fun I : Ideal A ↦ TopologicalRing.Ideal.IsWeakIdealOfDefinition I)
      (fun I ↦ (I : Set A)))

#check (TopologicalRing.exists_isWeakIdealOfDefinition_subset :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyPreadmissibleRing A] {U : Set A}, U ∈ nhds (0 : A) →
    ∃ I : Ideal A, TopologicalRing.Ideal.IsWeakIdealOfDefinition I ∧ (I : Set A) ⊆ U)

#check (TopologicalRing.hasBasis_isWeakIdealOfDefinition_mem_iff :
  ∀ {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsWeaklyPreadmissibleRing A] {U : Set A},
    U ∈ nhds (0 : A) ↔
      ∃ I : Ideal A, TopologicalRing.Ideal.IsWeakIdealOfDefinition I ∧ (I : Set A) ⊆ U)
