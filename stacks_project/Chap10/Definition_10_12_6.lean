/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Basic
import StacksCheckRecall

@[expose] public section

/-!
Definition 10.12.6: an `(A, B)`-bimodule is an abelian group with commuting `A`- and `B`-scalar
actions, represented canonically by `SMulCommClass A B N`.

@stack 00D1
-/

universe u v w

variable {A : Type u} {B : Type v} {N : Type w}
variable [Ring A] [Ring B] [AddCommGroup N]
variable [Module A N] [Module B N]

@[stacks 00D1 "commuting bimodule actions"]
#check @SMulCommClass
