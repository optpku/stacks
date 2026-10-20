module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Stackification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- The neutral data owner composes an explicitly localized cartesian map with the comparison of
a chosen inverse-image stack, without identifying the universes of the total categories. -/
#check @StackOver.InverseImage.Cartesian.pushforwardComparison
#check @StackOver.InverseImage.Cartesian.pushforwardComparison.toBasedFunctor
#check @StackOver.InverseImage.Cartesian.pushforwardComparison.toFunctor
#check @StackOver.InverseImage.Cartesian.pushforwardComparison.isStackification

/- The fixed-universe bundled companion retains the ambient fibred-category interface. -/
#check @StackOver.InverseImage.pushforwardComparison
#check @StackOver.InverseImage.pushforwardComparison.toCartesianBasedFunctor

/- The same result under the minimal pullback/equalizer hypotheses. -/
#check @StackOver.InverseImage.pushforwardComparison.isStackification

/- Lemma 8.12.11 (04WR): the canonical comparison map exhibits the chosen inverse-image stack
as a stackification of the pushed-forward fibred category. The source's terminal and pullback
assumptions use the equivalent finite-limit interface. -/
@[stacks 04WR]
#check @StackOver.InverseImage.pushforwardComparison.ofMorphismOfSites

/- The pushforward-composition theorem is also available before fixing the universes of any of
the three total categories. -/
#check @CartesianBasedFunctor.IsStackification.pushforward_comp
#check @FiberedCategoryOver.Hom.IsStackification.pushforward_comp

end CategoryTheory
