/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Int.XyEqSeven
import StacksCheckRecall

@[expose] public section

/- Exercise 111.58.6 -/
@[stacks 0D5L] #check
  (MvPolynomial.XyEqSeven.instIsRegularRing :
    IsRegularRing MvPolynomial.XyEqSeven.CoordinateRing)
