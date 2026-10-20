/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Hypercovering.Pullback
import StacksCheckRecall

/-!
# Lemma 25.7.1

The pullback construction and its matching-object comparison map are owned by the reusable
fixed-target hypercovering API.
-/

/- Lemma 25.7.1: a simplicial pullback along a map which is covering in degree zero and on every
matching pullback is again a hypercovering. -/
@[stacks 01GH]
#check @CategoryTheory.Hypercovering.pullback

/- The reusable construction exposes its underlying simplicial pullback. -/
#check @CategoryTheory.Hypercovering.pullback_toSimplicialObject

/- The higher hypothesis is phrased using the canonical comparison to the pullback of matching
objects. -/
#check @CategoryTheory.Hypercovering.matchingPullbackMap
#check @CategoryTheory.Hypercovering.matchingPullbackMap_fst
#check @CategoryTheory.Hypercovering.matchingPullbackMap_snd
