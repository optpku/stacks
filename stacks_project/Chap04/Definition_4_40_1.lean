/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Representable.Slice
import StacksCheckRecall

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids

/- Definition 4.40.1: a category fibred in groupoids over `C` is representable when it is
bicategorically equivalent over `C` to the canonical slice fibration for some `U : C`.
The main statement lives in the ordinary fixed `FiberedCategoryOver.Groupoids C` bicategory. -/
@[stacks 0046 "representable categories fibred in groupoids"]
#check (IsRepresentable (C := C) :
  ObjectProperty (FiberedCategoryOver.Groupoids C))

end FiberedCategoryOver.Groupoids

end CategoryTheory
