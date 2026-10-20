module

public import ReasLib.Algebra.Category.DifferentialGraded.Admissible.HomotopyExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 22.27.8 (09QP): null-homotopic boundary composites around a graded-split short
complex force the middle composite to be null-homotopic. -/
@[stacks 09QP]
#check ShortComplex.GradedSplitting.homotopic_comp_zero

/- The strict boundary-vanishing companion. -/
#check ShortComplex.GradedSplitting.comp_eq_zero
