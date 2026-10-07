module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Existence
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.8.1 (02ZN): a stackification comparison has Hom-presheaf sheafification maps and is
locally essentially surjective on objects. A target stack with these two properties exists and is
unique up to a uniquely compatible equivalence. -/
@[stacks 02ZN "(1) Hom-presheaf sheafification condition"]
#check @CartesianBasedFunctor.IsStackification.homSheafification
#check @Presheaf.IsSheafification
#check @Presheaf.IsSheafification.isSheaf
#check @Presheaf.IsSheafification.mem_W
#check @CartesianBasedFunctor.IsLocalEquivalence.homPresheafMap_mem

@[stacks 02ZN "(2) local essential-surjectivity condition"]
#check @CartesianBasedFunctor.LocallyEssentiallySurjective.iff_forall_cover

@[stacks 02ZN "existence of stackification"]
#check @Functor.IsFibered.Stackification.existsOverSite
#check @Functor.IsFibered.Stackification.Presentation
#check @Functor.IsFibered.Stackification.Presentation.of
#check @Functor.IsFibered.Stackification.Presentation.ofExists
#check @Functor.IsFibered.Stackification.Presentation.nonempty
#check @Functor.IsFibered.Stackification.presentation

@[stacks 02ZN "uniqueness of stackification"]
#check @CartesianBasedFunctor.IsStackification.comparisonUnique
#check @CartesianBasedFunctor.IsStackification.existsComparisonEquivalence

/- The uniqueness witness is also available as explicit comparison data.  These checks expose the
  Type-valued owner without replacing the proposition-level source statement. -/
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.of
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.ofExists
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.nonempty
#check @CartesianBasedFunctor.IsStackification.comparisonChoice
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.existsUniqueIso
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.comparisonIso
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.comparisonIso_spec
#check @CartesianBasedFunctor.IsStackification.ComparisonChoice.comparisonIso_unique

#check @CartesianBasedFunctor.IsStackification
#check @CartesianBasedFunctor.IsStackification.iff_isLocalEquivalence_and_isStack
#check @FiberedCategoryOver.Hom.IsStackification.isStack

end CategoryTheory
