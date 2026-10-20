/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import StacksCheckRecall

/-!
@stack 0165
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

/- Definition 14.2.1 (1): the injective order-preserving map that skips one index is the
canonical coface map. -/
@[stacks 0165 "Definition 14.2.1 (1)"]
#check (@SimplexCategory.δ :
  ∀ {n : ℕ}, Fin (n + 2) → (⦋n⦌ ⟶ ⦋n + 1⦌))

/- Definition 14.2.1 (2): the surjective order-preserving map that repeats one fiber is the
canonical codegeneracy map. -/
@[stacks 0165 "Definition 14.2.1 (2)"]
#check (@SimplexCategory.σ :
  ∀ {n : ℕ}, Fin (n + 1) → (⦋n + 1⦌ ⟶ ⦋n⦌))
