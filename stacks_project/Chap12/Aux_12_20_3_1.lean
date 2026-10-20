module

public import ReasLib.CategoryTheory.Homology.ShiftedDifferentialObject.Iteration
import StacksCheckRecall

@[expose] public section

/- Remark 12.20.3 (Variant) (0AMI): the reusable shifted-differential-object iteration API is
owned by ReasLib. -/

@[stacks 0AMI]
#check @CategoryTheory.ShiftedDifferentialObject.Differential.previous
#check @CategoryTheory.ShiftedDifferentialObject.Differential.shortComplex
#check @CategoryTheory.ShiftedDifferentialObject
#check @CategoryTheory.ShiftedDifferentialObject.shortComplex
#check @CategoryTheory.ShiftedDifferentialObject.homologyFunctor
#check @CategoryTheory.ShiftedDifferentialObject.Iteration.complex
#check @CategoryTheory.ShiftedDifferentialObject.Iteration.homologyIso
