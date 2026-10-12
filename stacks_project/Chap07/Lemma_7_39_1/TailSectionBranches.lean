/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement

/-!
# Compatibility import for refined presheaf fibers

Raw presheaf-fiber maps induced by a refinement are owned by
`DirectedRefinement.presheafFiberMap` and the lower
`RefinementFiber` API.  The former Chapter 7 tail-section implementation is
therefore retired in favor of those library owners.
-/

@[expose] public section
