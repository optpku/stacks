module

public import ReasLib.CategoryTheory.Monoidal.Closed.AdjunctionComparison
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry.RingedSpace

/- Remark 20.42.12 is the evaluation-compatibility square for the categorical internal-Hom
comparison.  Ringed-space instances specialize this owner to derived pushforwards. -/
@[stacks 0G7A]
#check @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison_evaluation_commSq

/- The transpose specification remains available alongside the square form. -/
#check @CategoryTheory.Adjunction.derivedPushforwardInternalHomComparison_spec

end AlgebraicGeometry.RingedSpace
