module

public import Mathlib.Topology.Algebra.LinearTopology
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible

/-!
# Weak ideals of definition as a neighbourhood basis

In a weakly pre-admissible ring, the weak ideals of definition form a
fundamental system of open neighbourhoods of `0`.
-/

@[expose] public section

universe u

open TopologicalRing

namespace TopologicalRing

/-- In a weakly pre-admissible ring, the weak ideals of definition form a
fundamental system of open neighbourhoods of `0`. -/
theorem hasBasis_isWeakIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsWeaklyPreadmissibleRing A] :
    (nhds (0 : A)).HasBasis (fun I : Ideal A ↦ Ideal.IsWeakIdealOfDefinition I)
      (fun I ↦ (I : Set A)) :=
  sorry

/-- Membership form of `hasBasis_isWeakIdealOfDefinition`: every neighbourhood of `0`
contains a weak ideal of definition. -/
theorem exists_isWeakIdealOfDefinition_subset {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsWeaklyPreadmissibleRing A] {U : Set A} (hU : U ∈ nhds (0 : A)) :
    ∃ I : Ideal A, Ideal.IsWeakIdealOfDefinition I ∧ (I : Set A) ⊆ U :=
  sorry

/-- Unfolding of `hasBasis_isWeakIdealOfDefinition` as a membership equivalence. -/
theorem hasBasis_isWeakIdealOfDefinition_mem_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsWeaklyPreadmissibleRing A] {U : Set A} :
    U ∈ nhds (0 : A) ↔
      ∃ I : Ideal A, Ideal.IsWeakIdealOfDefinition I ∧ (I : Set A) ⊆ U :=
  sorry

end TopologicalRing
