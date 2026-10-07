module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PowerSeries
import StacksCheckRecall

@[expose] public section

/-!
# Example 15.116.2: a purely inseparable extension of power-series DVRs

For a perfect field `k` of characteristic `p`, set `A = k[[X]]` and
`B = A[X^(1/p)]`.  The fraction field of `B` is used as the field `L` in
Definition 15.116.1.

@stack 09EP
-/

@[stacks 09EP "weak solutions are inseparable"]
#check @DVR.UniformizerRoot.PowerSeries.not_isSeparable_of_isWeakSolutionFor

@[stacks 09EP "finite inseparable extensions are solutions"]
#check @DVR.UniformizerRoot.PowerSeries.isSolutionFor_of_not_isSeparable
