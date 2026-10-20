/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DifferentialOperator.Generators
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.133.11

@stack 0G35

Lemma 10.133.11 (Tag 0G35): an order bound can be checked by taking scalar
commutators only with a family of algebra generators.  The reusable statement
is the generator criterion for `LinearMap.IsDifferentialOperatorOfOrder`.
-/

@[stacks 0G35 "differential operators checked on generators"]
#check @LinearMap.IsDifferentialOperatorOfOrder.of_generators
