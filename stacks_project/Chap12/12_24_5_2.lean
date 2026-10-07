module

public import ReasLib.Algebra.Category.ModuleCat.Filtration.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Equation 12.24.5.2

Compatibility facade for the graded piece of the ModuleCat cohomology filtration.
-/

/- Equation 12.24.5.2 [0BDT]: the induced cohomology graded piece is the quotient of filtered
cycles by next-stage cycles and filtered boundaries. -/
@[stacks 0BDT]
#check @ModuleCat.FilteredCohomology.GradedPiece.equiv

#check @ModuleCat.FilteredCohomology.GradedPiece.Presentation.quotient
#check @ModuleCat.FilteredCohomology.GradedPiece.equivStage
#check @ModuleCat.FilteredCohomology.GradedPiece.Presentation.equivQuotient
