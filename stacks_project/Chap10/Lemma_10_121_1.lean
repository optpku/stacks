/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.OrderOfVanishing.Basic
import StacksCheckRecall

/-!
# Lengths of principal quotients in dimension one

@stack 02MC

Lemma 10.121.1 uses `Ring.ord` for the length of a principal quotient; its
additivity and finite-length reformulation are recalled through their owners.
-/

@[expose] public section

@[stacks 02MC "(1), additivity owner"]
#check @Ring.ord_mul

@[stacks 02MC "(2), finite-length owner"]
#check @isFiniteLength_quotient_span_singleton

@[stacks 02MC "(2), length reformulation"]
#check @Module.length_ne_top_iff
