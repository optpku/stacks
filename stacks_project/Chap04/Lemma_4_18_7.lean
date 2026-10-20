/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Finite
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C]

/- Lemma 4.18.7: finite colimits, finite coproducts with coequalizers, and an initial object with
pushouts are equivalent conditions. -/
@[stacks 002Q]
#check (HasFiniteColimits.tfae C :
  [HasFiniteColimits C, HasFiniteCoproducts C ∧ HasCoequalizers C,
    HasInitial C ∧ HasPushouts C].TFAE)

end CategoryTheory.Limits
