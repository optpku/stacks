/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Action.VonNeumann

@[expose] public section

universe u

open CategoryTheory

/- Lemma 3.10.1. For a group whose carrier is the small type of elements of a ZFC set,
and a family of set-presented actions, an actual limit stage `G-Sets_α` contains the
family and the left-regular action and satisfies the bound and countable comparison API.
The ordinal is explicitly `Action.vonNeumannStageOrdinal` with the regular presentation.
Arbitrary native actions have canonical isomorphic set representatives; this does not
assert literal membership of every native isomorphic copy in the small stage. -/
@[stacks 000U] #check (Action.exists_vonNeumannStage :
  ∀ (A : ZFSet.{u}) [Group (Shrink A)] {ι : Type u}
    (S0 : ι → Action.SetPresentation (Shrink A)),
    ∃ α : Ordinal.{u}, Order.IsSuccLimit α ∧
      Action.IsSmallBoundClosed
        (Action.vonNeumannStage α : ObjectProperty (Action (Type u) (Shrink A))) ∧
      ∀ i, Action.vonNeumannStage α (S0 i).toAction)
