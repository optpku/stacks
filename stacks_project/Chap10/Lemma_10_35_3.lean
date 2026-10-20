/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Jacobson.Ring
import StacksCheckRecall

/-!
# Prime ideals as intersections of maximal ideals

@stack 00G2

Lemma 10.35.3 is the prime-ideal formulation of the canonical Jacobson-ring
criterion recalled below.
-/

@[expose] public section

@[stacks 00G2]
#check @isJacobsonRing_iff_sInf_maximal
