/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

namespace CategoryTheory

/- Lemma 8.10.3 (06NW) (1): the total functor is continuous for the two inherited topologies. -/
@[stacks 06NW "(1) continuity for inherited topologies"]
#check @CartesianBasedFunctor.inheritedTopology.isContinuous

#check @CartesianBasedFunctor.Inherited.isContinuous

/- Lemma 8.10.3 (06NW) (2): the total functor is cocontinuous for the two inherited
topologies. -/
@[stacks 06NW "(2) cocontinuity for inherited topologies"]
#check @CartesianBasedFunctor.inheritedTopology.isCocontinuous

#check @CartesianBasedFunctor.Inherited.isCocontinuous

/- Lemma 8.10.3 (06NW) (3): a cartesian functor between fibred categories over a common
site induces a morphism of the sheaf topoi for their inherited topologies. -/
@[stacks 06NW "(3) morphism of topoi from inherited topologies"]
#check @CartesianBasedFunctor.morphismOfTopoiIn

#check @CartesianBasedFunctor.Inherited.morphismOfTopoi

/- Lemma 8.10.3 (06NW) (4): the pushforward of the induced morphism is the canonical
cocontinuous pushforward. -/
@[stacks 06NW "(4) inherited-topology pushforward formula"]
#check @CartesianBasedFunctor.morphismOfTopoiIn.pushforward_eq

#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.pushforward_eq

/- Lemma 8.10.3 (06NW) (5): the inverse image of the induced morphism is the
canonical cocontinuous pullback. -/
@[stacks 06NW "(5) inherited-topology inverse-image formula"]
#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImage_eq

#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImage_eq

/- Lemma 8.10.3 (06NW) (6): the equality between the continuous and cocontinuous
inverse-image presentations is represented by an invertible natural comparison. -/
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageComparison

@[stacks 06NW "(6) inherited-topology inverse-image comparison"]
#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison.isIso

#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparison
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageComparison.isIso

/- The comparison can be promoted to an isomorphism from explicitly supplied inverse data. -/
#check @Functor.CocontinuousPullback.ComparisonIso.iso
#check @Functor.CocontinuousPullback.ComparisonIso.hom_eq
#check @Functor.CocontinuousPullback.ComparisonIso.eq

/- Lemma 8.10.3 (06NW) (7): the source's objectwise inverse-image formula is represented by a
deterministic natural comparison.  Its invertibility is Prop-valued; actual inverse data is
supplied explicitly by `ComparisonIso`. -/
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageEvalComparison

@[stacks 06NW "(7) objectwise inherited inverse-image formula"]
#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageEvalComparison.isIso
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageEvalIso.ofComparison
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageEvalIso.ofComparison.hom
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageEvalIso.ofComparison.eq

#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageEvalComparison
#check @CartesianBasedFunctor.Inherited.morphismOfTopoi.inverseImageEvalComparison.isIso
#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageEvalIso.ofComparison
#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageEvalIso.ofComparison.hom
#check @CartesianBasedFunctor.morphismOfTopoiIn.inverseImageEvalIso.ofComparison.eq

/- The source's inverse-image identification is an invertible natural comparison, not a literal
equality of functors. -/
#check @Functor.CocontinuousPullback.comparison
#check @Functor.CocontinuousPullback.comparison.isIso
#check @Functor.CocontinuousPullback.ComparisonIso
#check @Functor.CocontinuousPullback.ComparisonIso.ofIso

/- The underlying-presheaf form of the continuous inverse-image construction. -/
#check @Functor.sheafPushforwardContinuousCompSheafToPresheafIso

end CategoryTheory
