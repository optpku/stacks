/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.ScopedNS

/-!
# The Right Tensor-Product Algebra Scope

Mathlib provides `Algebra.TensorProduct.rightAlgebra` as the canonical algebra
action coming from the right tensor factor, but intentionally does not register
it globally: on a self-tensor product the left and right scalar actions are both
available.  This leaf makes precisely that existing action opt-in through
`open scoped Algebra.TensorProduct.Right`.

The owner is an attribute rather than a copied instance declaration, so a
consumer receives the exact mathlib instance and no second instance candidate
is introduced.
-/

@[expose] public section

open scoped TensorProduct

/-! The scope is intentionally limited to the right-oriented algebra action.  The compatible
`Algebra.TensorProduct.right_isScalarTower` is already supplied by mathlib once this exact action
is selected. -/
scoped[Algebra.TensorProduct.Right] attribute [instance] Algebra.TensorProduct.rightAlgebra
