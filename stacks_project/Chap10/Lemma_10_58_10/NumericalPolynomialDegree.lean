/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical.Degree
import StacksCheckRecall

/-!
# Numerical-polynomial degree comparison

@stack 00K3
-/

@[expose] public section

@[stacks 00K3 "degree of the multichoose comparison function"]
#check @IsNumericalPolynomial.degreeLT.multichoose_sub

@[stacks 00K3 "degree transfer under eventual domination"]
#check @IsNumericalPolynomial.degreeLT.of_eventually_nonneg_le
