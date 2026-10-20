/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family.Sheaf.Refinement
public import ReasLib.CategoryTheory.Sites.Point.Refinement

/-!
# Compatibility import for branch separation

The source proof's finite branch-product calculation is not a stable public
construction.  Downstream code should use
`DirectedRefinement.Separates.existsCoverLift`, whose statement records
the resulting separating refinement directly.
-/

@[expose] public section
