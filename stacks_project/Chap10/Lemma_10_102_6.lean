/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.TrivialSum.Rank
import StacksCheckRecall

/-!
# Ranks of the differentials in a split finite free complex

@stack 00MW
-/

@[stacks 00MW "(1)"]
#check @FiniteFreeComplex.IsTrivialSum.exteriorRank_diffAt

@[stacks 00MW "(2)"]
#check @FiniteFreeComplex.IsTrivialSum.exteriorRank_diffAt_add

@[stacks 00MW "(3)"]
#check @FiniteFreeComplex.IsTrivialSum.rankMinorIdeal_diffAt
