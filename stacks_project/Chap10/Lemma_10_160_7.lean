/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.CohenRing.Truncation
import StacksCheckRecall

@[expose] public section

/-!
# Formal smoothness of truncated Cohen rings

Lemma 10.160.7 is owned by the positive-power truncation API for Cohen rings.  This source file
recalls the algebra statement together with its characteristic and ring-hom views.

@stack 0329
-/

@[stacks 0329 "characteristic of the truncation"]
#check @IsCohenRing.quotient_span_residueChar_pow_charP

@[stacks 0329]
#check @IsCohenRing.zmodPow_quotient_formallySmooth

@[stacks 0329 "ring-hom view"]
#check @IsCohenRing.zmodPow_quotient_algebraMap_formallySmooth
