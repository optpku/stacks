/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Topology
public import ReasLib.CategoryTheory.Sites.TopologyComparison.Absolute
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint

import StacksCheckRecall

@[expose] public section

/-!
[stacks 0EWI]

Example 7.14.3 is the identity morphism of sites induced by an inclusion of Grothendieck
topologies.
-/

#check CategoryTheory.Functor.id_isContinuous_of_le
@[stacks 0EWI] #check CategoryTheory.IsMorphismOfSites.id_of_le

/- For the identity functor between the two topologies, this is the concrete inverse-image
functor obtained by sheafifying a sheaf for the coarser topology. -/
@[stacks 0EWI "identity-site inverse-image functor"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.pullback

/- Its adjunction with the forgetful direct image identifies the left adjoint whose exactness is
recorded above. -/
@[stacks 0EWI "inverse-image/direct-image adjunction"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.adjunction

@[stacks 0EWI "exactness of the identity-site inverse image"]
#check @CategoryTheory.GrothendieckTopology.TopologyComparison.pullback_exact
