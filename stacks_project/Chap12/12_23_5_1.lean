module

public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Equation 12.23.5.1 [012F] is the one-object specialization of the morphism-level eventual
cycle representative inequality. -/
@[stacks 012F]
#check FilteredObject.Hom.Representative.Cycle.kernel_le_eventual
