module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.8.2: the universal factorization through a stackification is the
universe-polymorphic lift theorem for cartesian based functors. -/
@[stacks 0435 "universal factorization through stackification"]
#check @CartesianBasedFunctor.IsStackification.lift
#check @CartesianBasedFunctor.IsStackification.liftIsoUnique
#check @CartesianBasedFunctor.IsStackification.LiftChoice
#check @CartesianBasedFunctor.IsStackification.LiftChoice.of
#check @CartesianBasedFunctor.IsStackification.LiftChoice.ofExists
#check @CartesianBasedFunctor.IsStackification.LiftChoice.nonempty
#check @CartesianBasedFunctor.IsStackification.liftChoice
#check @CartesianBasedFunctor.IsStackification.liftChoiceComparison
#check @CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso
#check @CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso_spec
#check @CartesianBasedFunctor.IsStackification.LiftChoice.comparisonIso_unique

/- The bundled fixed-universe specialization used by `FiberedCategoryOver`. -/
#check @FiberedCategoryOver.Hom.IsStackification.lift
#check @FiberedCategoryOver.Hom.IsStackification.liftIsoUnique
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice.of
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice.ofExists
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice.nonempty
#check @FiberedCategoryOver.Hom.IsStackification.liftChoice
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice.comparisonIso
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice.comparisonIso_spec
#check @FiberedCategoryOver.Hom.IsStackification.LiftChoice.comparisonIso_unique

end CategoryTheory
