/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleCloseds.Hausdorff
public import Mathlib.Topology.KrullDimension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Krull Dimension of Hausdorff Spaces

The topological Krull-dimension consequences of Hausdorff separation.
-/

@[expose] public section

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Every nonempty Hausdorff space has topological Krull dimension zero. -/
@[stacks 0056 "nonempty Hausdorff spaces have topological Krull dimension zero"]
theorem topologicalKrullDim_eq_zero_of_nonempty_t2 [T2Space X] [Nonempty X] :
    topologicalKrullDim X = 0 := by
  letI : Nonempty (IrreducibleCloseds X) := ‹Nonempty X›.map fun x ↦
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  unfold topologicalKrullDim
  apply le_antisymm
  · rw [Order.krullDim_nonpos_iff_forall_isMax]
    intro Z Y hZY
    obtain ⟨z, rfl⟩ := Z.exists_eq_singleton
    obtain ⟨y, rfl⟩ := Y.exists_eq_singleton
    have hset : ({z} : Set X) ⊆ {y} := hZY
    have hzy : z = y := Set.mem_singleton_iff.mp (hset (Set.mem_singleton z))
    subst y
    exact le_rfl
  · exact Order.krullDim_nonneg
