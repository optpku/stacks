/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.FittingIdeal.Basic
import StacksCheckRecall

/-!
# Definition 15.8.3

@stack 07Z9
-/

@[expose] public section

/-!
# Fitting Ideals

This chapter entry re-exports the neutral Fitting-ideal infrastructure.
-/

/- Definition 15.8.3: for a finite module, the `k`th Fitting ideal is computed
from any surjective finite free presentation; the convention in degree `-1` is
the zero ideal. -/
#check @presentationFittingIdeal
#check @presentationFittingIdeal_eq_of_surjective
#check @SurjectivePresentation
@[stacks 07Z9 "intrinsic Fitting ideals"]
#check @fittingIdeal
#check @fittingIdealNegOne
#check @precedingFittingIdeal
#check @fittingIdeal_eq_presentationFittingIdeal
#check @fittingIdeal_eq_of_linearEquiv
