module

public import ReasLib.CategoryTheory.Sites.BeckChevalley

import StacksCheckRecall

@[expose] public section

/-!
[stacks 0FN1]

Lemma 7.28.6 is the finality criterion for the direct-image/inverse-image
Beck-Chevalley comparison of a square of sites.
-/

#check CategoryTheory.CatCommSq.BeckChevalley.comparison
@[stacks 0FN1] #check CategoryTheory.CatCommSq.BeckChevalley.comparison_isIso_of_final
