module

public import ReasLib.CategoryTheory.Sites.HigherDirectImage.Colimits
import StacksCheckRecall

@[expose] public section

/- Lemma 21.16.4 (0H7B): the local covering criterion for the canonical colimit comparison of a
higher direct image is the reusable site-level theorem below. -/
@[stacks 0H7B]
#check @CategoryTheory.Sheaf.HigherDirectImage.colimitComparison_isIso_of_cover
