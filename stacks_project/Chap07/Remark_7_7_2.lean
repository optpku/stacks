module

public import ReasLib.CategoryTheory.Sites.Sheaf.Empty

import StacksCheckRecall

@[expose] public section

/-!
[stacks 04B3]

Remark 7.7.2 is the empty-presieve characterization of terminal section types.
-/

@[stacks 04B3] #check CategoryTheory.Presieve.isSheafFor_empty_iff_nonempty_isTerminal
#check CategoryTheory.Presieve.isSheafFor_empty_of_uniqueSections
