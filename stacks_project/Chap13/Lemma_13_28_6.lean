/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.K0.Bifunctor
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Lemma 13.28.6 (Stacks 0FCT): a bifunctor that is triangulated in each
variable induces a biadditive map on triangulated zeroth Grothendieck groups. -/

@[stacks 0FCT]
#check @CategoryTheory.TriangulatedK0.Bifunctor.map

@[stacks 0FCT]
#check @CategoryTheory.TriangulatedK0.Bifunctor.map_of_left

@[stacks 0FCT]
#check @CategoryTheory.TriangulatedK0.Bifunctor.map_of

@[stacks 0FCT]
#check @CategoryTheory.TriangulatedK0.Bifunctor.flip_map_of
