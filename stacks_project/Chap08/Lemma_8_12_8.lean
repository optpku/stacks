/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward.Hom.Fibered.Equivalence
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map.TwoCell
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.8 (04WI): the canonical pushforward-pullback Hom functor is an equivalence. The
universe-polymorphic cartesian Hom functor is the reusable owner. -/
#check @FiberedCategoryOver.Pushforward.CartesianHom.functor
@[stacks 04WI "pushforward-pullback Hom equivalence"]
#check @FiberedCategoryOver.Pushforward.CartesianHom.functor.isEquivalence

/- The fixed-owner functor and its equivalence instance are application-facing companions. -/
#check @FiberedCategoryOver.Pushforward.homFunctor
#check @FiberedCategoryOver.Pushforward.homFunctor.isEquivalence

/- The reusable inversion-choice hierarchy and its Hom-functor actions. -/
#check @Functor.Pushforward.InversionChoice
#check @Functor.Pushforward.InversionChoice.canonical
#check @CartesianBasedFunctor.Pushforward.InversionChoice
#check @CartesianBasedFunctor.Pushforward.InversionChoice.ofProjectionChoices
#check @FiberedCategoryOver.Pushforward.InversionChoice
#check @FiberedCategoryOver.Pushforward.MapInversionChoice
#check @FiberedCategoryOver.Pushforward.MapInversionChoice.canonical
#check @FiberedCategoryOver.Pushforward.InversionChoice.ofProjectionChoices
#check @FiberedCategoryOver.Pushforward.InversionChoice.toCartesian
#check @Functor.Pushforward.map.ofInversionChoice
#check @CartesianBasedFunctor.Pushforward.map.ofInversionChoice
#check @FiberedCategoryOver.Pushforward.map.ofInversionChoice
#check @CartesianBasedFunctor.Pushforward.mapFunctor
#check @FiberedCategoryOver.Pushforward.mapFunctor

/- Projection-level strong-cartesianness criteria used by the Hom equivalence. -/
#check @Limits.CategoricalPullback.Left.isStronglyCartesian_of_snd
#check @Limits.CategoricalPullback.Left.snd_isStronglyCartesian_of_left
#check @Limits.CategoricalPullback.Left.isStronglyCartesian_iff_snd

end CategoryTheory
