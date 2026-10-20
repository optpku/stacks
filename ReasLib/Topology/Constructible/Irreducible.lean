/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import ReasLib.Topology.IrreducibleCloseds.FiniteLocallyClosed

/-!
# Constructible Traces on Irreducible Closed Sets

This module provides constructibility criteria expressed through traces on
irreducible closed subspaces.
-/

@[expose] public section

universe u

open Set Topology TopologicalSpace
open scoped Set.Notation

namespace Topology

variable {X : Type u} [TopologicalSpace X]

/-- A constructible subset has, on every irreducible closed trace, either a nonempty open
subtrace or a non-dense trace. -/
@[stacks 053Z "constructible irreducible-trace dichotomy"]
theorem IsConstructible.exists_nonemptyOpen_subset_trace_or_not_dense {E : Set X}
    (hE : IsConstructible E) (Z : IrreducibleCloseds X) :
    (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
      ¬ Dense ((Z : Set X) ↓∩ E) := sorry

variable [NoetherianSpace X]

/-- A subset of a Noetherian space is constructible exactly when all of its irreducible closed
traces satisfy the open-or-not-dense dichotomy. -/
@[stacks 053Z]
theorem IsConstructible.iff_forall_irreducibleClosed (E : Set X) :
    IsConstructible E ↔
      ∀ Z : IrreducibleCloseds X,
        (∃ U : Opens Z, (U : Set Z).Nonempty ∧ (U : Set Z) ⊆ (Z : Set X) ↓∩ E) ∨
          ¬ Dense ((Z : Set X) ↓∩ E) := sorry

end Topology
