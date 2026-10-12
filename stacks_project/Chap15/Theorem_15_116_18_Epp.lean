/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Epp
import StacksCheckRecall

@[expose] public section

/-!
# Theorem 15.116.18 (Epp)

The reusable Epp existence statement is owned by IsWeakSolutionFor.exists_of_epp. This file is
the source-facing tagged bridge and contains no duplicate proof helpers or chapter-specific owner.

@stack 09F9
-/

@[stacks 09F9 "Theorem 15.116.18: Epp weak-solution existence"]
#check @IsWeakSolutionFor.exists_of_epp

#check @IsWeakSolutionFor
