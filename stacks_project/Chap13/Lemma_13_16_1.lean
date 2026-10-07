module

import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Bounds
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.16.1 (Stacks 05TC): pointwise right-derived values preserve lower
cohomological bounds, and upper truncation is unchanged on cohomology throughout
the retained range. -/

@[stacks 05TC]
#check @CategoryTheory.Functor.RightDerived.Value.isGE

@[stacks 05TC]
#check @CategoryTheory.Functor.RightDerived.Value.TruncLE.homologyMap_isIso
