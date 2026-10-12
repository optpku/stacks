/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.CostructuredArrowTopology.Topos
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Legacy import compatibility for the 7.28.5 comma-site support tree.  The
public owner is `CostructuredArrow.CocontinuousOver` in ReasLib. -/
@[stacks 0D5R "comma-site direct image"] #check @CategoryTheory.CostructuredArrow.CocontinuousOver.directImageComparison_nonempty
