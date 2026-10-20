module

public import ReasLib.Topology.Constructible.Irreducible

/-!
# Neighborhood and Openness Tests for Constructible Sets

This module packages the irreducible-closed trace criteria for neighborhoods
and open subsets in Noetherian spaces.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X]

/-- Lemma 5.16.4: a constructible subset is a neighborhood of a point exactly when every
irreducible closed subspace through that point has dense trace. -/
@[stacks 0540]
theorem IsConstructible.mem_nhds_iff_forall_dense_irreducibleCloseds_trace
    {E : Set X} (hE : IsConstructible E) {x : X} :
    E ∈ 𝓝 x ↔
      ∀ Z : IrreducibleCloseds X, x ∈ Z → Dense ((Z : Set X) ↓∩ E) := sorry

/-- Lemma 5.16.5: a subset of a Noetherian space is open exactly when every irreducible closed
trace is empty or contains a nonempty open subspace. -/
@[stacks 0541]
theorem isOpen_iff_forall_irreducibleCloseds_inter_empty_or_contains_nonempty_open (E : Set X) :
    IsOpen E ↔
      ∀ Z : IrreducibleCloseds X,
        ((Z : Set X) ↓∩ E) = ∅ ∨
          ∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E := sorry

end Topology
