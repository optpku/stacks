/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.CategoryHomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Example 21.39.1 (08PF): category homology is the left-derived colimit of an additive
presheaf on a category over a point. -/
@[stacks 08PF "category homology as a derived colimit"]
#check @CategoryTheory.CategoryHomology.categoryHomology
