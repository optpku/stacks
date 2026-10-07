module

public import StacksCheckRecall.CommandCrossRef

public import ReasLib.CategoryTheory.Sites.Localization.Representable.LowerShriek
import StacksCheckRecall

@[expose] public section

/- Lemma 7.30.5 (0792): after identifying sheaves on `C / U` with objects over
`J.sheafifiedRepresentable U`, the forgetful functor is the localization lower shriek; its
comparison with `Over.star` is invertible. -/
@[stacks 04IQ "(1)"] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.comparison.forget

@[stacks 04IQ "(2)"] #check @CategoryTheory.GrothendieckTopology.RepresentableLocalization.lowerShriekOverPullbackComparison_isIso
