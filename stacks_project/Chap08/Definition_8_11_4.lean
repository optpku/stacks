/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Over
import StacksCheckRecall

@[expose] public section

/-!
# Definition 8.11.4 -- Gerbes over stacks

The canonical owner is the universe-polymorphic
`CartesianBasedFunctor.IsGerbeMorphism`; its specialization in `StackOver.Groupoids.Hom` records
the same two local conditions for morphisms of stacks in groupoids, without committing the source
entry to one chosen factorization model or a common universe for total categories.
-/

namespace CategoryTheory

/- Definition 8.11.4: a relative gerbe is a morphism of stacks in groupoids that is locally
essentially surjective on objects and locally lifts fiber morphisms. -/
#check @CartesianBasedFunctor.IsGerbeMorphism
#check @CartesianBasedFunctor.isGerbeMorphism_iff
#check @CartesianBasedFunctor.isGerbeMorphism_iff_localConditions
#check @CartesianBasedFunctor.LocallyEssentiallySurjective
#check @CartesianBasedFunctor.Homwise.IsLocallySurjective
#check @CartesianBasedFunctor.LocallyLifts
#check @CartesianBasedFunctor.LocallyLifts.iff_forall_cover
#check @FiberedCategoryOver.Hom.IsGerbeMorphism
@[stacks 06P2 "gerbes over a stack"]
#check @StackOver.Groupoids.Hom.IsGerbeMorphism
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.iff_localConditions
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.locallyEssentiallySurjective
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.homwiseLocallySurjective
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.locallyLifts
#check @StackOver.Groupoids.Hom.IsGerbeMorphism.iff_factorization

end CategoryTheory
