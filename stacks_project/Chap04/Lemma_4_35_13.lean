/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.Slice

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable {U : C} (p : S ⥤ Over U)
variable [Functor.IsFibered.InGroupoids (p ⋙ Over.forget U)]

/- Lemma 4.35.13: if `p : S ⥤ Over U` becomes fibred in groupoids after composing with
`Over.forget U`, then `p` is fibred in groupoids over the slice. -/
@[stacks 02XT]
#check (IsFibered.InGroupoids.of_compOverForget p :
  IsFibered.InGroupoids p)

end CategoryTheory.Functor
