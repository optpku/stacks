/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Valuation.Nonzero
import StacksCheckRecall

/-!
# Lemma 10.50.14

@stack 00IF
-/

@[stacks 00IF "nonzero valuation owner"]
#check @ValuationRing.nonzeroValuation

@[stacks 00IF "additive normalization"]
#check @ValuationRing.nonzeroValuation_toAdd_nonneg

@[stacks 00IF "(1)"]
#check @ValuationRing.nonzeroValuation_eq_one_iff_isUnit

@[stacks 00IF "(2)"]
#check @ValuationRing.nonzeroValuation_mul

@[stacks 00IF "(3)"]
#check @ValuationRing.nonzeroValuation_add_le_max
