/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Galois.SetValued
import StacksCheckRecall

@[expose] public section

universe vC uC w

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable (F : C ⥤ Type w)

/- Definition 58.3.6 -/
@[stacks 0BMY] #check (CategoryTheory.Functor.IsGalois F : Prop)

end CategoryTheory
