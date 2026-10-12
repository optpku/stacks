/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generic Points of Irreducible Closed Sets

This module adds source-independent generic-point characterizations to Mathlib's
`IsGenericPoint`, `T0Space`, and `QuasiSober` API.
-/

@[expose] public section

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- A point is generic for the whole space exactly when its singleton closure is the whole
space. -/
theorem isGenericPoint_univ_iff_eq_closure (x : X) :
    IsGenericPoint x Set.univ ↔ (Set.univ : Set X) = closure ({x} : Set X) := by
  rw [isGenericPoint_def]
  exact eq_comm

/-- A point is generic for an irreducible closed subset exactly when it belongs to that
subset and its singleton closure equals the subset. -/
@[stacks 004X "generic points of irreducible closed subsets"]
theorem IrreducibleCloseds.isGenericPoint_iff_mem_and_eq_closure_singleton
    (Z : IrreducibleCloseds X) (x : X) :
    IsGenericPoint x (Z : Set X) ↔
      x ∈ (Z : Set X) ∧ (Z : Set X) = closure {x} := sorry

/-- A space is `T0` and quasi-sober exactly when each irreducible closed subset has a
unique generic point. -/
@[stacks 004X "sober spaces via unique generic points"]
theorem sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint :
    (T0Space X ∧ QuasiSober X) ↔
      ∀ Z : IrreducibleCloseds X, ∃! x : X, IsGenericPoint x (Z : Set X) := sorry

/-- Every irreducible closed subset of a sober `T0` space has a unique generic point. -/
@[stacks 01IS]
theorem TopologicalSpace.IsIrreducible.existsUnique_isGenericPoint
    [QuasiSober X] [T0Space X] {Z : Set X} (hZ : IsIrreducible Z)
    (hZclosed : IsClosed Z) :
    ∃! x : X, IsGenericPoint x Z := sorry

/-- Every irreducible closed subset of a `T0` space has at most one generic point. -/
theorem TopologicalSpace.IsIrreducible.subsingleton_isGenericPoint
    [T0Space X] {Z : Set X} (hZ : IsIrreducible Z) (hZclosed : IsClosed Z) :
    Set.Subsingleton {x : X | IsGenericPoint x Z} := sorry
