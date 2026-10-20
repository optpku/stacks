module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.Representable.LowerShriek
import StacksCheckRecall

@[expose] public section

/- Lemma 7.25.7 (03EE): under representable localization, lower shriek after slice pullback is
canonically the slice functor `Over.star`. -/
@[stacks 03EE] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.lowerShriekOverPullbackComparison_isIso
