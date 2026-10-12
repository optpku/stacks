/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.FiniteExtension
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.1 (0GLR)

This source file keeps the legacy repository path `Lemma_15_117_1`; the reusable theorem is owned
by `IsSolutionFor.of_finite_extension` in ReasLib.

@stack 0GLR
-/

/- Lemma 15.117.1: finite extension stability of the solution predicate. -/
@[stacks 0GLR "Lemma 15.117.1: finite extension stability of solutions"]
#check @IsSolutionFor.of_finite_extension

#check @IsSolutionFor
#print axioms IsSolutionFor.of_finite_extension

end
