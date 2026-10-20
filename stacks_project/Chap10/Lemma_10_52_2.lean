/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Length
import StacksCheckRecall

/-!
# Finite generation from finite length

Lemma 10.52.2 states that a module of finite length is finitely generated.

@stack 02LZ
-/

@[expose] public section

/- Lemma 10.52.2 (Tag 02LZ): a module whose `Module.length` is strictly below `⊤` is finite. -/
@[stacks 02LZ]
#check @Module.finite_of_length_lt_top

/- Canonical `≠ ⊤` and predicate-level entry points for downstream reuse. -/
@[stacks 02LZ "canonical length criterion"]
#check @Module.finite_of_length_ne_top

@[stacks 02LZ "finite-length predicate bridge"]
#check @Module.Finite.of_isFiniteLength
