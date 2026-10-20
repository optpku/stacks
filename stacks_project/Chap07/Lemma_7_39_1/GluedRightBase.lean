/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Point.Refinement

/-!
# Compatibility import for glued refinements

The former sum-index and right-base witnesses were implementation details of
one proof.  `DirectedRefinement` is the reusable owner: it exposes the target
inverse system, restriction isomorphism, fiber map, separation predicate, and
cover-lift result without committing downstream clients to a chosen gluing.
-/

@[expose] public section
