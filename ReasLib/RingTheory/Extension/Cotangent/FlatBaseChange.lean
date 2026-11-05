/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Extension.Cotangent.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change for first cotangent homology

For an `R`-algebra `S` and a flat `R`-algebra `T`, the canonical comparison is
`T ⊗[R] Algebra.H1Cotangent R S ≃ₗ[T] Algebra.H1Cotangent T (T ⊗[R] S)`.
Both the source ring and the target algebra change under base change, as in
Stacks tag `00S4`.

This module re-exports Mathlib's `Algebra.tensorH1CotangentOfFlat` and its
pure-tensor computation rule `Algebra.tensorH1CotangentOfFlat_tmul`.
-/

@[expose] public section

#check @Algebra.tensorH1CotangentOfFlat

#check @Algebra.tensorH1CotangentOfFlat_tmul
