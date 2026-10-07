module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.Composition
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.116.4

The four ascent and descent clauses are source-facing recalls of the reusable composition API.
The quotient-field normalization in clauses (3) and (4) is owned by
`DVR.BaseChange.IsWeakSolutionOnFactor` and `DVR.BaseChange.IsSolutionOnFactor`.

@stack 09ES
-/

@[stacks 09ES "Lemma 15.116.4 (1)"]
#check @weakSolutionFor_of_weakSolutionFor_comp

@[stacks 09ES "Lemma 15.116.4 (2)"]
#check @solutionFor_of_solutionFor_comp

@[stacks 09ES "Lemma 15.116.4 (3)"]
#check @weakSolutionFor_comp_of_weakSolutionFor_of_reducedTensorProductFactors

@[stacks 09ES "Lemma 15.116.4 (4)"]
#check @solutionFor_comp_of_solutionFor_of_reducedTensorProductFactors

#check @DVR.BaseChange.IsWeakSolutionOnFactor
#check @DVR.BaseChange.IsSolutionOnFactor
