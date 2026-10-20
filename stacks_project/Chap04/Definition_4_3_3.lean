/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Types.Basic
import StacksCheckRecall

@[expose] public section

universe w v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

/-
Definition 4.3.3: a presheaf of sets on a category `C` is a contravariant functor
`Cᵒᵖ ⥤ Type w`, and its morphisms are natural transformations. Mathlib already uses this functor
category itself as the canonical owner, so no project alias is introduced.
-/
@[stacks 02X6 "set-valued presheaves as functors from the opposite category"]
#check (Cᵒᵖ ⥤ Type w)

end CategoryTheory
