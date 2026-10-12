/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.PrecompLift
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Lift
public import ReasLib.CategoryTheory.Fibered.Stack.Hom.Precomposition.Stackification
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.8.3: precomposition by a stackification gives an equivalence of hom-categories into
every stack. -/
@[stacks 04W9 "hom-category universal property of stackification"]
#check @CartesianBasedFunctor.IsStackification.precomp_isEquivalence

#check @CartesianBasedFunctor.precomp
#check @FiberedCategoryOver.Hom.IsStackification.precomp_isEquivalence
#check @StackOver.Hom.precomp
#check @StackOver.Hom.precomp_isEquivalence
#check @Bicategory.precomp

/- Downstream constructions that must retain the selected inverse use the explicit
quasi-inverse lift API rather than choosing data from the proposition above. -/
#check @CartesianBasedFunctor.PrecompLift.mapFunctor
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.obj
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.map
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso.hom.app
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.comparisonIso.inv.app
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.choiceIso
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.choiceIso.comparison
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.choiceIso.refl
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.choiceIso.trans
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.isoOfComparison
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.isoOfComparison.comparison
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.isoOfComparison.eq_iff
#check @CartesianBasedFunctor.PrecompLift.mapFunctor.isoOfComparison.self

/- The fixed-universe stack-Hom API specializes the same neutral construction. Its owner name
records that explicit quasi-inverse data, rather than a stackification proof, is the input. -/
#check @StackOver.Hom.PrecompLift.mapFunctor
#check @StackOver.Hom.PrecompLift.mapFunctor.obj
#check @StackOver.Hom.PrecompLift.mapFunctor.map
#check @StackOver.Hom.PrecompLift.mapFunctor.comparisonIso
#check @StackOver.Hom.PrecompLift.mapFunctor.comparisonIso.hom.app
#check @StackOver.Hom.PrecompLift.mapFunctor.comparisonIso.inv.app
#check @StackOver.Hom.PrecompLift.mapFunctor.choiceIso
#check @StackOver.Hom.PrecompLift.mapFunctor.choiceIso.comparison
#check @StackOver.Hom.PrecompLift.mapFunctor.choiceIso.refl
#check @StackOver.Hom.PrecompLift.mapFunctor.choiceIso.trans
#check @StackOver.Hom.PrecompLift.targetFunctor
#check @StackOver.Hom.PrecompLift.targetFunctor.map_app
#check @StackOver.Hom.PrecompLift.targetFunctor.comparisonNatIso
#check @StackOver.Hom.PrecompLift.targetFunctor.choiceIso
#check @StackOver.Hom.PrecompLift.targetFunctor.choiceIso.comparison
#check @StackOver.Hom.PrecompLift.mapFunctor.isoOfComparison
#check @StackOver.Hom.PrecompLift.mapFunctor.isoOfComparison.comparison
#check @StackOver.Hom.PrecompLift.mapFunctor.isoOfComparison.eq_iff

end CategoryTheory
