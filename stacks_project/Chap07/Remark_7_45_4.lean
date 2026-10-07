module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Topos.BaseChange

@[expose] public section

open CategoryTheory
open scoped TwoSquare

namespace CategoryTheory

/- Remark 7.45.4 (0F6Y): horizontal composition of base-change maps is already the generic
`MorphismOfTopoiIn` statement below. A specialization to ringed topoi belongs with the genuine
`RingedSite` owner and its structure-sheaf data in Chapter 18, rather than introducing a
site-only surrogate here. -/
@[stacks 0F6Y] #check @MorphismOfTopoiIn.baseChange_hcomp

end CategoryTheory
