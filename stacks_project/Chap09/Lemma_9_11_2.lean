/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

universe u

variable {k : Type u} [Field k]

/- Lemma 9.11.2: coprimeness is detected by the absence of a common zero in an algebraic closure. -/
@[stacks 09GY]
#check (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed
    k (AlgebraicClosure k) :
  ∀ p q : k[X], IsCoprime p q ↔
    ∀ a : AlgebraicClosure k, p.aeval a ≠ 0 ∨ q.aeval a ≠ 0)
