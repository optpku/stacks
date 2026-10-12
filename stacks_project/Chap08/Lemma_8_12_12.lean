/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InverseImage.Comparison
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.12.12 (1) (tag 04WS): the neutral owner constructs a heterogeneous cartesian
comparison directly from pushforward projection and comparison data.  Its inverse-image
specialization is an equivalence under the invariant form of Sites, Lemma 7.21.8. -/
#check @CartesianBasedFunctor.PushforwardHom.pullbackComparison
#check @StackOver.InverseImage.Cartesian.pullbackComparison

#check @StackOver.InverseImage.Cartesian.pullbackComparison.isEquivalence

/- The fixed-universe bundled morphism is the source-facing canonical comparison; the neutral
heterogeneous specialization remains available as a companion for universe-polymorphic consumers. -/
#check @StackOver.InverseImage.pullbackComparison
#check @StackOver.InverseImage.pullbackComparison.toCartesianBasedFunctor
#check @StackOver.InverseImage.pullbackComparison.toMorIso

@[stacks 04WS "(1) fixed-universe pullback comparison equivalence"]
#check @StackOver.InverseImage.pullbackComparison.isEquivalence

/- Lemma 8.12.12 (2) (tag 04WS): for two chosen inverse-image stacks, inverse image canonically
induces an equivalence of their heterogeneous cartesian Hom categories.  The quasi-inverse of the
forward pushforward Hom equivalence is selected inside the shared owner. -/
@[stacks 04WS "(2) pointwise inverse-image Hom equivalence"]
#check @StackOver.InverseImage.Cartesian.pointwiseMapHom.isEquivalence

#check @StackOver.InverseImage.Cartesian.pointwiseMapHom
#check @StackOver.InverseImage.Cartesian.pointwiseMapHom.obj
#check @StackOver.InverseImage.Cartesian.pointwiseMapHom.map
#check @StackOver.InverseImage.Cartesian.pointwiseMapHom.comparisonIso
#check @StackOver.InverseImage.Cartesian.pointwiseMapHom.comparisonIso.hom.app
#check @StackOver.InverseImage.Cartesian.pointwiseMapHom.comparisonIso.inv.app

/- The explicit-choice heterogeneous API remains available when a consumer must control or
compare the selected quasi-inverse. -/
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.comparisonIso
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.comparisonIso.hom.app
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.comparisonIso.inv.app
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.choiceIso
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.choiceIso.hom.app
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.choiceIso.inv.app
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.choiceIso.comparison
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.isoOfComparison
#check @CartesianBasedFunctor.PushforwardHom.mapFunctor.isoOfComparison.eq_iff
#check @StackOver.InverseImage.Cartesian.pushforwardHom
#check @StackOver.InverseImage.Cartesian.pushforwardHom.isEquivalence
#check @StackOver.InverseImage.Cartesian.mapHom
#check @StackOver.InverseImage.Cartesian.mapHom.obj
#check @StackOver.InverseImage.Cartesian.mapHom.map
#check @StackOver.InverseImage.Cartesian.mapHom.comparisonIso.hom.app
#check @StackOver.InverseImage.Cartesian.mapHom.comparisonIso.inv.app
#check @StackOver.InverseImage.Cartesian.mapHom.choiceIso
#check @StackOver.InverseImage.Cartesian.mapHom.choiceIso.hom.app
#check @StackOver.InverseImage.Cartesian.mapHom.choiceIso.inv.app
#check @StackOver.InverseImage.Cartesian.mapHom.choiceIso.comparison
#check @StackOver.InverseImage.Cartesian.mapHom.isoOfComparison
#check @StackOver.InverseImage.Cartesian.mapHom.isoOfComparison.eq_iff

#check @StackOver.InverseImage.Cartesian.mapHom.isEquivalence

/- A coherent choice for all objects and Hom categories upgrades the pointwise construction to a
global pseudofunctor.  Its local-equivalence theorem is stronger coherence data, not the main
source-facing content of clause (2). -/
#check @StackOver.InverseImage.PseudofunctorChoice
#check @StackOver.InverseImage.PseudofunctorChoice.pushforwardChoice
#check @StackOver.InverseImage.PseudofunctorChoice.mapFunctor.obj
#check @StackOver.InverseImage.PseudofunctorChoice.mapFunctor.map
#check @StackOver.InverseImage.PseudofunctorChoice.prelax.obj
#check @StackOver.InverseImage.PseudofunctorChoice.prelax.map
#check @StackOver.InverseImage.PseudofunctorChoice.prelax.map₂
#check @StackOver.InverseImage.CoherentPseudofunctorChoice
#check @StackOver.InverseImage.pseudofunctor
#check @StackOver.InverseImage.pseudofunctor.isLocallyEquivalence

/- The fixed-universe direct presentation remains available to consumers already holding a
pushforward inversion family and a stackification quasi-inverse. -/
#check @StackOver.InverseImage.mapHom
#check @StackOver.InverseImage.mapHom.obj
#check @StackOver.InverseImage.mapHom.map
#check @StackOver.InverseImage.mapHom.choiceIso
#check @StackOver.InverseImage.mapHom.inversionChoiceIso
#check @StackOver.InverseImage.mapHom.homFunctorIso

#check @StackOver.InverseImage.mapHom.isEquivalence

/- The Hom-equivalence presentation remains available under a distinct name when a consumer
already owns a quasi-inverse of the forward Hom functor. -/
#check @StackOver.InverseImage.mapHom.ofHomQuasiInverse
#check @StackOver.InverseImage.mapHom.homQuasiInverseIso

end CategoryTheory
