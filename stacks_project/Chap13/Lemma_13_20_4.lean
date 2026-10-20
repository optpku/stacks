module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived
import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Functoriality
import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Augmented.Functoriality
import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Sequence.Augmented.Model
import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.Universal
import Mathlib.CategoryTheory.Abelian.RightDerived
import StacksCheckRecall

@[expose] public section

/- Lemma 13.20.4 is a recall block for the standard five-term homology
sequence, the degree-zero and injective-acyclicity facts for ordinary right
derived functors, and the acyclicity-based universality criterion for the
bounded-below derived delta functor.  In particular, the source item does not
introduce a second, placeholder-valued cohomological delta functor. -/

@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.cohomological.exactWindow
@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.cohomological.exactWindow_exact
@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.Bounded.degree.isZero_of_neg
@[stacks 015B] #check @CategoryTheory.Functor.rightDerivedZeroIsoSelf
@[stacks 015B] #check @CategoryTheory.Functor.isZero_rightDerived_obj_injective_succ
@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.Universal.ofAcyclic
@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.Universal.ofHasMonoEmbedding
@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.Universal.ofComparison
@[stacks 015B] #check @CategoryTheory.Functor.RightDerived.Bounded.cohomological_isUniversal
#check @CategoryTheory.CohomologicalDeltaFunctor.IsUniversal.desc
#check @CategoryTheory.CohomologicalDeltaFunctor.IsUniversal.iso
#check @CategoryTheory.CohomologicalDeltaFunctor.exactWindow
#check @CategoryTheory.CohomologicalDeltaFunctor.exactWindow_exact
#check @CategoryTheory.CohomologicalDeltaFunctor.exactWindowMap.app_zero
#check @CategoryTheory.CohomologicalDeltaFunctor.exactWindow.modelFunctor
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow_exact
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.map
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.modelMap
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.modelMap_δ₀
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.modelMap_app_six
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.functor
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.modelFunctor
#check @CategoryTheory.CohomologicalDeltaFunctor.augmentedWindow.functor_comp_δ₀
#check @CategoryTheory.Functor.RightDerived.cohomological.degreeIso
#check @CategoryTheory.Functor.RightDerived.delta.map
#check @CategoryTheory.Functor.RightDerived.delta.mapIso
#check @CategoryTheory.Functor.RightDerived.cohomological.map
#check @CategoryTheory.Functor.RightDerived.cohomological.map_app_eq_degree
#check @CategoryTheory.Functor.RightDerived.cohomological.mapIso
#check @CategoryTheory.Functor.RightDerived.cohomological.connecting
#check @CategoryTheory.Functor.RightDerived.cohomological.exactWindow.map
#check @CategoryTheory.Functor.RightDerived.cohomological.exactWindow.functor
#check @CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow
#check @CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow_exact
#check @CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow.map
#check @CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow.functor
#check @CategoryTheory.Functor.RightDerived.cohomological.augmentedWindow.functor_comp_δ₀

end
