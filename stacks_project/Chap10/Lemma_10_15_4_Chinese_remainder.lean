/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.ChineseRemainder
import StacksCheckRecall

/-!
# Lemma 10.15.4 (Chinese remainder)

@stack 00DT
-/

@[expose] public section

/- Lemma 10.15.4 (Chinese remainder) (1): for pairwise comaximal ideals,
their product equals their intersection. -/
@[stacks 00DT "(1), product/intersection"]
#check @Ideal.ChineseRemainder.prod_eq_iInf

/- Lemma 10.15.4 (Chinese remainder) (2): quotienting by the product of a
pairwise comaximal family is equivalent to the product of the quotients. -/
@[stacks 00DT "(2), quotient equivalence"]
#check @Ideal.ChineseRemainder.quotientProdEquiv

@[stacks 00DT "(2), quotient equivalence evaluation"]
#check @Ideal.ChineseRemainder.quotientProdEquiv_apply_mk

@[stacks 00DT "intersection-form companion"]
#check @Ideal.quotientInfRingEquivPiQuotient
