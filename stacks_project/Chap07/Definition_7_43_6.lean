/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Closed
public import StacksCheckRecall.CommandCrossRef

/-!
# Definition 7.43.6

The closed-subtopos object property is named in ReasLib and indexed by the
canonical bundled category of subterminal sheaves.
-/

@[expose] public section

/- Definition 7.43.6 (08LZ): the closed subtopos associated to a subterminal
sheaf consists of the objects for which the product projection is an
isomorphism. -/
@[stacks 08LZ] #check @CategoryTheory.GrothendieckTopology.closedSubtopos

@[stacks 08LZ] #check @CategoryTheory.GrothendieckTopology.IsClosedSubtopos

@[stacks 08LZ] #check @CategoryTheory.GrothendieckTopology.IsClosedSubtopos.exists_subterminal
