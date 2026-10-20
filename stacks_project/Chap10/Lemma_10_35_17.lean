/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
public import ReasLib.RingTheory.Ideal.Quotient.Maximal
import StacksCheckRecall

/-!
# Jacobson quotients and their maximal ideals

@stack 00G9
-/

@[expose] public section

@[stacks 00G9 "(1), Jacobson quotient"]
#check @isJacobsonRing_quotient

@[stacks 00G9 "(2), maximal-ideal correspondence"]
#check @Ideal.Quotient.orderIsoOfMaximal

@[stacks 00G9 "contraction under the correspondence"]
#check @Ideal.Quotient.orderIsoOfMaximal_apply_val

@[stacks 00G9 "extension under the inverse correspondence"]
#check @Ideal.Quotient.orderIsoOfMaximal_symm_apply_val
