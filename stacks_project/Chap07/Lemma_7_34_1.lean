/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Functor.PresheafFiber.Pushforward

/-!
# Fibers of pushforward presheaves

This chapter-facing recall uses the general Kan-extension/fiber comparison in
`ReasLib`. The source label `0F4F` is attached to
`Functor.lanCompPresheafFiberIso`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

/- Lemma 7.34.1: for `u : C ⥤ D` and `v : D ⥤ Type`, the fiber for `v` of
the left Kan extension along `u.op` is the fiber for the composite `u ⋙ v`. -/
@[stacks 0F4F] #check @Functor.lanCompPresheafFiberIso

end CategoryTheory
