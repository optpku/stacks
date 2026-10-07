module

import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Triangle
import StacksCheckRecall

@[expose] public section

/- Lemma 13.40.3: in a distinguished triangle, left orthogonality of the first object is
equivalent to locality of the second map. -/
@[stacks 0H0M] #check
  @CategoryTheory.ObjectProperty.LeftOrthogonal.obj₁_iff_local
