/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.19: any irreducible subset of a topological space `X` is contained in an
irreducible component of `X`. -/
@[stacks 02DA]
#check (exists_mem_irreducibleComponents_subset_of_isIrreducible :
  ∀ {X : Type*} [TopologicalSpace X] (s : Set X), IsIrreducible s →
    ∃ u ∈ irreducibleComponents X, s ⊆ u)
