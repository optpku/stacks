/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Topos.Subtopos.Slice
public import StacksCheckRecall.CommandCrossRef

/-!
# Definition 7.43.4

Slice presentations and the open-subtopos predicate are ReasLib API.  The
presentation data is explicit there, while its ordinary use is the
proposition-level `PresentsSlice` predicate.
-/

@[expose] public section

/- Definition 7.43.4 (08LX): an open subtopos is the essential image of the
direct image of a presentation of the slice at a subterminal sheaf. -/
@[stacks 08LX] #check @CategoryTheory.MorphismOfTopoiIn.SlicePresentation

@[stacks 08LX] #check @CategoryTheory.MorphismOfTopoiIn.PresentsSlice

@[stacks 08LX] #check @CategoryTheory.GrothendieckTopology.OpenSubtoposPresentation

@[stacks 08LX] #check @CategoryTheory.GrothendieckTopology.OpenSubtoposPresentation.presentsSlice

@[stacks 08LX] #check @CategoryTheory.GrothendieckTopology.OpenSubtoposPresentation.toSubtoposPresentation

@[stacks 08LX] #check @CategoryTheory.GrothendieckTopology.IsOpenSubtopos

@[stacks 08LX] #check @CategoryTheory.GrothendieckTopology.IsOpenSubtopos.isSubtopos
