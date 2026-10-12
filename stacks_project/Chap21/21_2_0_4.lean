/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.Sheaf

/- 21.2.0.4 (071F): a higher direct image is computed by applying sheaf pushforward to a
chosen injective resolution and taking homology. -/
@[stacks 071F "higher direct image from an injective resolution"]
#check @Sheaf.HigherDirectImage.isoHomologyPushforward

/- The functor and object owners used by the comparison. -/
#check @Sheaf.higherDirectImageFunctor
#check @Sheaf.higherDirectImage
