/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Pair.BaseChange
import StacksCheckRecall

/-!
# Integral base change for pair Henselization

This file recalls Lemma 15.12.7 and its explicit tensor comparison from the reusable owner.

@stack 0DYE
-/

@[expose] public section

-- The concrete comparison whose bijectivity is asserted by the source lemma.
@[stacks 0DYE "Henselization tensor comparison"]
#check @RingPairCat.henselizationBaseChangeComparison

-- Lemma 15.12.7: integral base change identifies the two pair Henselizations.
@[stacks 0DYE "Lemma 15.12.7"]
#check @RingPairCat.henselizationBaseChangeComparison_bijective_of_isIntegral
