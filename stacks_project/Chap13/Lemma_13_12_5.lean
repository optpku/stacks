module

import ReasLib.CategoryTheory.DerivedCategory.Truncation.ComposableArrows
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 13.12.5 (`08Q2`): the two source-facing factorization statements are owned by the
neutral derived truncation API.  Their proof details belong to the implementation of that API,
not to the chapter entry. -/
@[stacks 08Q2] #check
  @CategoryTheory.DerivedCategory.Truncation.ComposableArrows.Cochain.exists_truncLE
@[stacks 08Q2] #check
  @CategoryTheory.DerivedCategory.Truncation.ComposableArrows.Cochain.exists_truncGE

/- The shifted, fully general core statements are the preferred downstream interface. -/
@[stacks 08Q2] #check
  @CategoryTheory.DerivedCategory.Truncation.ComposableArrows.exists_truncLE
@[stacks 08Q2] #check
  @CategoryTheory.DerivedCategory.Truncation.ComposableArrows.exists_truncGE

/- The one-step statements are the reusable induction primitives. -/
@[stacks 08Q2] #check
  @CategoryTheory.DerivedCategory.TruncLE.exists_lift_of_homologyMap_eq_zero
@[stacks 08Q2] #check
  @CategoryTheory.DerivedCategory.TruncGE.exists_desc_of_homologyMap_eq_zero
