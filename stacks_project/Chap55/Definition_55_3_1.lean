/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap55.Definition_55_3_1_NumericalType

/- Definition 55.3.1: a numerical type consists of a positive finite number of
indices, positive multiplicities and weights, nonnegative component genera, and
a symmetric integral intersection matrix whose off-diagonal entries are
nonnegative, whose support is connected, whose weighted row sums vanish, and
whose row entries are divisible by the corresponding weights. -/
@[stacks 0C6Z] #check (NumericalType : Type)
