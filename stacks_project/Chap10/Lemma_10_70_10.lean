/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.BlowupChart.Domain
import StacksCheckRecall

/-!
# Lemma 10.70.10 recall

@stack 052R

The domain result is a reusable instance for nonzero chart parameters.
-/

@[expose] public section

/- Lemma 10.70.10 (052R): an affine blowup chart of a domain at a nonzero
parameter is a domain. -/
@[stacks 052R] #check @AffineBlowupChart.instIsDomain
@[stacks 052R "nonzero-parameter domain instance"]
#check @AffineBlowupChart.instIsDomainOfNonzero
