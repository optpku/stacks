/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.FiniteConnected.Basic
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/- Lemma 4.18.5: finite connected colimits are equivalent to coequalizers and pushouts. -/
@[stacks 04AV]
#check (HasFiniteConnectedColimits.Pushouts.iff_coequalizers C :
  HasFiniteConnectedColimits C ↔ HasCoequalizers C ∧ HasPushouts C)

end CategoryTheory.Limits
