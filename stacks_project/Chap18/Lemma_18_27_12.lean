module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 18.27.12

The source hypothesis is owned at the site level; the reusable module-sheaf API exposes both
functorial preservation and categorical finite presentability.
-/

@[expose] public section

/- Lemma 18.27.12 (0GN0), functor form: `coyoneda.obj (op F)` preserves filtered
colimits. -/
@[stacks 0GN0 "preservation"]
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.preservesHom_of_testSet

/- Lemma 18.27.12 (0GN0), canonical object form: `F` is finitely presentable. -/
@[stacks 0GN0 "finitely presentable object"]
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.isFinitelyPresentable_of_testSet

/- Lemma 18.27.12 (0GN0), fixed-diagram form: the canonical Hom comparison is an
isomorphism. -/
@[stacks 0GN0 "fixed diagram"]
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.hom_isIso_of_testSet

#check @SheafOfModules.IsFinitePresentation.FilteredColimit.homComparison
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.homComparison_ι
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.homComparisonInv
#check @SheafOfModules.IsFinitePresentation.FilteredColimit.homComparisonIso
