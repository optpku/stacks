module

import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Triangle
import StacksCheckRecall

@[expose] public section

/- Lemma 13.40.2: in a distinguished triangle, right orthogonality of the third object is
equivalent to colocality of the first map. -/
@[stacks 0CQQ] #check
  @CategoryTheory.ObjectProperty.RightOrthogonal.obj₃_iff_colocal
