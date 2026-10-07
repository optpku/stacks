module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.Representable.Relocalization
import StacksCheckRecall

@[expose] public section

/- 04IS (Lemma 7.30.7): this is exactly the canonical mate comparison
`RepresentableLocalization.relocalizationInverseImageOverPullback J f` and its `IsIso` theorem
from Lemma 7.25.9. -/
@[stacks 04IS "(1)"] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.relocalizationInverseImageOverPullback

@[stacks 04IS "(2)"] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.relocalizationInverseImageOverPullback_isIso
