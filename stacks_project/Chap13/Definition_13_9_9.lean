/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Homology.DegreewiseSplit
import StacksCheckRecall

@[expose] public section

/-!
# Definition 13.9.9

The source notion is the existence property `ShortComplex.IsDegreewiseSplit`; it does not choose
a splitting.  Chosen families are obtained through `isDegreewiseSplit_iff` only when the
connecting map or associated triangle is constructed.
-/

namespace CategoryTheory.ShortComplex

@[stacks 014I]
#check @IsDegreewiseSplit
@[stacks 014I]
#check @isDegreewiseSplit_iff
@[stacks 014I]
#check @isDegreewiseSplit_of_splitting

end CategoryTheory.ShortComplex

namespace CochainComplex

@[stacks 014I]
#check @homOfDegreewiseSplit
@[stacks 014I]
#check @triangleOfDegreewiseSplit
@[stacks 014I]
#check @trianglehOfDegreewiseSplit

end CochainComplex
