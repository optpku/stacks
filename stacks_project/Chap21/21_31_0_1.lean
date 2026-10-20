/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.LCCat.SmallToSlice.Abelian
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Sheaf
import StacksCheckRecall

@[expose] public section

/- Definition 21.31.0.1: the small-site and localized-slice inverse/direct images are recalled
from their canonical ReasLib owners.  The former chapter-local `pi/a` aliases were wrappers with
no downstream users; consumers should import the canonical declarations directly. -/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open TopologicalSpace
open scoped CategoryTheory CategoryTheory.GrothendieckTopology

noncomputable section

/- Generic site-level inverse and direct image owners. -/
#check @CategoryTheory.Functor.sheafPullback
#check @CategoryTheory.Functor.sheafPushforwardContinuous
#check @CategoryTheory.GrothendieckTopology.comparisonTopologyPullback
#check @CategoryTheory.GrothendieckTopology.comparisonTopologyPushforward
#check @CategoryTheory.GrothendieckTopology.comparisonTopologyAdjunction

/- Canonical Type-valued small-to-slice inverse-image owners. -/
#check @LCCat.SmallToSlice.typePullback
#check @LCCat.SmallToSlice.qcTypePullback

/- Concrete `LCCat` small-to-slice owners. -/
#check @LCCat.SmallToSlice.smallPullback
#check @LCCat.SmallToSlice.smallPullbackExact
#check @LCCat.SmallToSlice.abPullback
#check @LCCat.SmallToSlice.abPushforward
#check @LCCat.SmallToSlice.abAdjunction
#check @LCCat.SmallToSlice.abPullbackPlus
#check @LCCat.SmallToSlice.aInverseAb
#check @CategoryTheory.GrothendieckTopology.comparisonTopologyPullbackAb
#check @CategoryTheory.GrothendieckTopology.comparisonTopologyPushforwardAb

end
