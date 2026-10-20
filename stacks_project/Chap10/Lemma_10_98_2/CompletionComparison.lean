/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.InverseSystem
import StacksCheckRecall

@[expose] public section

/-!
# Completion Comparisons for Positive Systems

The completion comparison used by the former local proof is now the generic
cone-based shared API.

@stack 09B8
-/

@[stacks 09B8 "adic-completion comparison from a cone"]
#check @CategoryTheory.PNatInverseSystem.Cone.adicCompletionComparison

@[stacks 09B8 "completion-to-limit comparison"]
#check @CategoryTheory.PNatInverseSystem.completionToLimit
