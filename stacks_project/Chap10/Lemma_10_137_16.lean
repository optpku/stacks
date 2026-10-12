/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.AtPrime.Fiber

@[expose] public section

/-!
# Lemma 10.137.16

@stack 00TF
-/

/- Lemma 10.137.16, tag 00TF: the reusable pointwise criterion is
`Algebra.SmoothAtPrime.FiberCriterion`; its principal theorem is
`Algebra.SmoothAtPrime.of_fiberCriterion`.  The source's unbundled
three-hypothesis spelling is retained as the companion constructor
`Algebra.SmoothAtPrime.of_fiber`. -/
@[stacks 00TF "smoothness at a prime from a local smooth fiber"]
#check @Algebra.SmoothAtPrime.FiberCriterion

@[stacks 00TF "smoothness at a prime from a local smooth fiber"]
#check @Algebra.SmoothAtPrime.of_fiberCriterion

@[stacks 00TF "smoothness at a prime from a local smooth fiber"]
#check @Algebra.SmoothAtPrime.of_fiber
