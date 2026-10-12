/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Orthogonal.Triangle
import StacksCheckRecall

@[expose] public section

/- Lemma 13.40.2: in a distinguished triangle, right orthogonality of the third object is
equivalent to colocality of the first map. -/
@[stacks 0CQQ] #check
  @CategoryTheory.ObjectProperty.RightOrthogonal.obj₃_iff_colocal
