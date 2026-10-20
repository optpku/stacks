/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.HomotopyCategory
import StacksCheckRecall

/-! # Homotopy after refining a hypercovering -/

/- Lemma 25.9.2 (01GS): parallel hypercovering morphisms become directly simplicially
homotopic after precomposition with a refinement. -/
@[stacks 01GS] #check @CategoryTheory.Hypercovering.existsHomotopyRefinement

#check @CategoryTheory.Hypercovering.IsHomotopyRefinement
#check @CategoryTheory.Hypercovering.IsHomotopyRefinement.homotopic
