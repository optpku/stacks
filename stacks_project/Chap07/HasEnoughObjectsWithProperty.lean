/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef

-- Compatibility import for downstream statements written before the neutral owner was extracted.
public import ReasLib.CategoryTheory.Sites.EnoughObjects
import StacksCheckRecall

@[expose] public section

/- Definition 7.40.2 (090L): a site has enough objects satisfying `P` when every object has a
covering by objects satisfying `P`. The canonical owner is in ReasLib. -/
@[stacks 090L "(3)"] #check @CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty
