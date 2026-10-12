/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.BaseChange

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory
/- Remark 7.45.3 (0F6X): vertical composition of base-change maps is a
universe-polymorphic `MorphismOfTopoiIn` API in ReasLib. -/
@[stacks 0F6X] #check @MorphismOfTopoiIn.baseChange_vcomp

end CategoryTheory
