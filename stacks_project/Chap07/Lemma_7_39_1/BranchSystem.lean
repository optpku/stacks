/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement

/-!
# Compatibility import for branch refinements

The old tail-and-branch construction was proof-local machinery for
Lemma 7.39.1.  Its reusable semantic owner is `DirectedRefinement`, together
with `OrderedRefinement` and `DirectedPreorderSystem`, in
`ReasLib.CategoryTheory.Sites.Point.Refinement`.
-/

@[expose] public section
