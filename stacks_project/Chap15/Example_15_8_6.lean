/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.FittingIdeal.Quotient

/-!
# Example 15.8.6

@stack 0H73
-/

@[expose] public section

/- Example 15.8.6 (1) (0H73): the zeroth Fitting ideal of a quotient is the quotient ideal. -/
@[stacks 0H73 "zeroth Fitting ideal of a quotient"]
#check @FittingIdeal.quotientAtZero

/- Example 15.8.6 (2) (0H73): the zeroth Fitting ideal of a product of two quotient modules is
the product ideal. -/
@[stacks 0H73 "zeroth Fitting ideal of a product of quotients"]
#check @FittingIdeal.quotientProdAtZero

/- Example 15.8.6 (3) (0H73): the first Fitting ideal of a product of two quotient modules is
the sum ideal. -/
@[stacks 0H73 "first Fitting ideal of a product of quotients"]
#check @FittingIdeal.quotientProdAtOne
