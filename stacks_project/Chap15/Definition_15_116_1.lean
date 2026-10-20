module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.116.1

The reusable owner is IsWeakSolutionFor, with the formal-smooth and separable companions
IsSolutionFor and IsSeparableSolutionFor. Their reduced tensor-product branch data and
maximal-ideal criterion live in ReasLib, so this chapter file remains a thin, source-traceable
entry.

@stack 09EN
-/

@[stacks 09EN "Definition 15.116.1 (1): weak solution"]
#check @IsWeakSolutionFor

#check @DVR.BaseChange.Branch.IsWeakSolution
#check @DVR.BaseChange.Branch.IsSolution
#check @DVR.BaseChange.Branch
@[stacks 09EN "Definition 15.116.1 (2): solution"]
#check @IsSolutionFor
@[stacks 09EN "Definition 15.116.1 (3): separable solution"]
#check @IsSeparableSolutionFor
#check @IsWeakSolutionFor.branch_spec
#check @IsWeakSolutionFor.iff_forall_ideals
#check @IsWeakSolutionFor.iff_map_maximalIdeal
#check @IsSolutionFor.branch_spec
#check @IsSolutionFor.iff_forall_ideals
