/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Forgetful.TwoCell
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.5.5 — Bridge

Definition 8.5.5 defines the `2`-category of stacks in groupoids over a site: its objects are
stacks in groupoids, its `1`-morphisms are morphisms over the base, and its `2`-morphisms are
vertical transformations. The canonical full-subbicategory owner is
`CategoryTheory.StackOver.Groupoids`.
-/

namespace CategoryTheory

@[stacks 02ZK]
#check @StackOver.Groupoids

-- Objects are read in the ambient `2`-category of groupoid-fibred categories.
#check @StackOver.Groupoids.toGroupoids

-- `1`-morphisms are the ambient morphisms over `C`.
#check @StackOver.Groupoids.Hom.toGroupoidsMor

-- `2`-morphisms are the ambient vertical transformations.
#check @StackOver.Groupoids.Hom₂.toGroupoidsNatTrans

end CategoryTheory
