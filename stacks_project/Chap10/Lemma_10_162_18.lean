/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.PthRoot
import StacksCheckRecall

@[expose] public section

/-!
@stack 09E2

# Descent of p-th roots from the completion

This file records the source-facing statement. The Nagata and analytically
unramified infrastructure is owned by ReasLib and recalled below.
-/

/-! Lemma 10.162.18: let `(A, m)` be a Noetherian local Nagata domain whose
fraction field has characteristic `p`. If `a : A` has a `p`-th root in the
maximal-ideal completion of `A`, then it already has a `p`-th root in `A`. -/
@[stacks 09E2]
#check @NagataRing.exists_pth_root_of_completion

@[stacks 032R "Nagata owner"]
#check @NagataRing

@[stacks 0331 "analytically unramified Nagata domain"]
#check @NagataRing.analyticallyUnramified

@[stacks 032X "completion reducedness owner"]
#check @IsAnalyticallyUnramified

#check @AdicCompletion
