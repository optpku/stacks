/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Point.Construction

/-!
# Canonical recall for Proposition 7.33.3

The cover-lifting predicate and construction of a site point from a left exact
`Type`-valued functor are reusable site-level API, owned by ReasLib rather than
by this Chapter 7 presentation file.
-/

@[expose] public section

/- Proposition 7.33.3 (00YC): a set-valued functor on a site with finite limits is the
fiber of a site point exactly when it preserves finite limits and lifts elements through every
covering sieve. -/
@[stacks 00YC] #check @CategoryTheory.GrothendieckTopology.Point.Fiber.exists_iff
