/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Enough

@[expose] public section

namespace CategoryTheory.GrothendieckTopology

/- Definition 7.38.1 (00YK): an indexed family of points is conservative precisely when its
stalk functors jointly reflect isomorphisms; a site has enough points precisely when it admits a
small conservative indexed family.  These are the reusable `PointFamily` and
`HasEnoughPoints` interfaces. -/
@[stacks 00YK] #check @PointFamily.isConservative_iff

@[stacks 00YK] #check @HasEnoughPoints.iff_exists_indexedConservativeFamily

end CategoryTheory.GrothendieckTopology
