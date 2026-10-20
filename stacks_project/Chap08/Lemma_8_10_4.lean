/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InheritedTopology.InGroupoids
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

/- Lemma 8.10.4 (tag 0CN0) (1): a groupoid-fibred projection induces an equivalence from the
slice at `x` to the slice of the base at its image. -/
@[stacks 0CN0 "(1) equivalence of slice categories"]
#check @Functor.IsFibered.InGroupoids.overPost.isEquivalence

/- Lemma 8.10.4 (tag 0CN0) (2): under the slice equivalence, a sieve is covering for the
inherited slice topology exactly when its image is covering for the base slice topology. -/
@[stacks 0CN0 "(2) correspondence of covering sieves"]
#check @Functor.inheritedTopology.overPost.covering_iff

/- The projection API is owned first at the level of arbitrary selected precoverages. -/
#check @Precoverage.StronglyCartesianLift.Projection.le_comap
#check @Precoverage.StronglyCartesianLift.Projection.isPrecoverageContinuous
#check @Precoverage.StronglyCartesianLift.Projection.hasCoverLifts
#check @Precoverage.StronglyCartesianLift.Projection.isContinuous
#check @Precoverage.StronglyCartesianLift.Projection.isCocontinuous

/- Specializing the neutral projection API gives continuity, cocontinuity, and the standard
structure-valued direct-image statement for every fibred projection. -/
#check @Functor.inheritedTopology.isContinuous
#check @Functor.inheritedTopology.isCocontinuous
#check @Functor.inheritedTopology.coverPreserving
#check @CoverPreserving.cover_preserve
#check @Functor.cover_lift

/- For groupoid fibrations, all arrows are strongly cartesian; this gives the stronger
continuity statement for the saturated canonical precoverages. -/
#check @Functor.inheritedTopology.isPrecoverageContinuous
#check @Functor.IsFibered.InGroupoids.Pullback.preservesWalkingCospan
#check @Functor.Precoverage.IsContinuous.ofGrothendieck
#check @Functor.Precoverage.IsContinuous.toLeComap
#check @Functor.inheritedTopology.overPost.isMorphismOfSites
#check @Functor.inheritedTopology.overPost.isDenseSubsite

end CategoryTheory
