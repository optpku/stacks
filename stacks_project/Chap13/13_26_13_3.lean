module

import ReasLib.CategoryTheory.Filtration.IntervalSplit.Injective
import StacksCheckRecall

@[expose] public section

/-!
# Equation 13.26.13.3

The interval-presentation predicate is the formal owner of the decomposition
`I ≅ ⨁ p, I_p` and its tail filtration.  The underlying filtered object, its stage formula, and
the canonical stage isomorphism are exposed separately for downstream computations.
-/

namespace CategoryTheory.FilteredObject.IntervalSplit

/- Equation 13.26.13.3 (`015T`): a finite filtered-injective object admits an injective interval
presentation. -/
@[stacks 015T] #check @FilteredInjective.hasPresentation

/- The presentation predicate owns the finite interval, injective summands, and filtered
isomorphism occurring in the equation. -/
#check @HasInjectivePresentation

/- The canonical presentation has the interval biproduct as its underlying object. -/
#check @filteredObject

/- Its `p`-th filtration stage is the canonical tail subobject. -/
#check @filtration_obj

/- The tail subobject is canonically the biproduct of the summands indexed by `q ≥ p`. -/
#check @Stage.iso

end CategoryTheory.FilteredObject.IntervalSplit
