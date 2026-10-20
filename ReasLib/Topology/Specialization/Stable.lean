module

public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Directed Closed Presentations

Specialization-stable subsets admit a directed presentation by bundled closed
subsets.  The bundled `Closeds` index avoids a parallel closed-set predicate.
-/

@[expose] public section

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.19.3: a subset is stable under specialization exactly when it is
the union of a directed family of bundled closed subsets. -/
@[stacks 0EES]
theorem stableUnderSpecialization_iff_exists_directedCloseds_sUnion_eq {T : Set X} :
    StableUnderSpecialization T ↔
      ∃ S : Set (Closeds X), DirectedOn (· ≤ ·) S ∧
        ⋃₀ ((fun Z : Closeds X ↦ (Z : Set X)) '' S) = T := sorry
