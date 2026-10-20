module

public import Mathlib.Topology.Algebra.LinearTopology
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

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

/-- Every neighbourhood of zero contains a weak ideal of definition. -/
theorem exists_isWeakIdealOfDefinition_subset {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsWeaklyPreadmissibleRing A] {U : Set A} (hU : U ∈ nhds (0 : A)) :
    ∃ I : Ideal A, Ideal.IsWeakIdealOfDefinition I ∧ (I : Set A) ⊆ U :=
  sorry

/-- A set is a neighbourhood of zero exactly when it contains a weak ideal of definition. -/
theorem hasBasis_isWeakIdealOfDefinition_mem_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsWeaklyPreadmissibleRing A] {U : Set A} :
    U ∈ nhds (0 : A) ↔
      ∃ I : Ideal A, Ideal.IsWeakIdealOfDefinition I ∧ (I : Set A) ⊆ U :=
  sorry

end TopologicalRing
