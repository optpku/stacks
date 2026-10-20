/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GenericFlatness.Locus
import StacksCheckRecall

@[expose] public section

/-!
# The Generic-Flatness Good Locus

The displayed union defining the good locus is recalled from its canonical
ReasLib equation.

@stack 051V
-/

/- Equation 10.118.3.2: `U(R → S, M)` is the union of the basic opens `D(f)`
over the elements `f : R` satisfying the localization condition 051U. -/
@[stacks 051V]
#check @GenericFlatness.goodLocus_eq_iUnion
