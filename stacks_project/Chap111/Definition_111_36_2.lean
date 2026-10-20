/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 111.36.2: on a topological space `X`, a point `x` is a specialization of
`x'` iff `x ∈ closure {x'}`. This is the canonical relation `Specializes`, written
`x' ⤳ x` in mathlib binder order; mathlib's `specializes_iff_mem_closure` identifies it
with membership in the closure of the singleton `{x'}`. -/
@[stacks 029P]
#check (specializes_iff_mem_closure :
  ∀ {X : Type u} [TopologicalSpace X] {x' x : X},
    x' ⤳ x ↔ x ∈ closure ({x'} : Set X))
