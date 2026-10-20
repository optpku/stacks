/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Map
import StacksCheckRecall

/-!
# Lemma 25.12.5 compatibility

The degreewise image construction for fixed-target formal-coproduct hypercoverings is owned by
`ReasLib.CategoryTheory.Sites.Hypercovering.Map`.  This file retains the chapter import path and
the source label without duplicating a categorical construction.
-/

/- Lemma 25.12.5: a continuous pullback-preserving functor sends a hypercovering of `Y` to a
hypercovering of `u.obj Y` by applying `u` degreewise. -/
@[stacks 0DAZ]
#check @CategoryTheory.Functor.Hypercovering.map

/- The reusable construction exposes its degreewise simplicial object and computation rule. -/
#check @CategoryTheory.Functor.Hypercovering.simplicial
#check @CategoryTheory.Functor.Hypercovering.map_toSimplicialObject
