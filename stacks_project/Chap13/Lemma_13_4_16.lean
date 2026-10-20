module

import ReasLib.CategoryTheory.Pretriangulated.Subcategory.Characterization
import StacksCheckRecall

@[expose] public section

/- Lemma 13.4.16 is owned by `ObjectProperty.IsTriangulated` and its reusable `trW` bridge. -/
@[stacks 05QX] #check @CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero
@[stacks 05QX] #check @CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift
@[stacks 05QX] #check @CategoryTheory.ObjectProperty.trW_of_isTriangulated
@[stacks 05QX] #check
  @CategoryTheory.ObjectProperty.isTriangulated_of_containsZero_of_isStableUnderShift_of_trW

end
