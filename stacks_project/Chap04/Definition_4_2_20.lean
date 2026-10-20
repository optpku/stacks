/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Products.Basic
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C]
variable (D : Type u₂) [Category.{v₂} D]

/-
Definition 4.2.20: for categories `C` and `D`, the product type `C × D` carries the canonical
product category `prod'`. Its objects are pairs, while the underlying structure `prod C D` makes
each morphism a pair of component morphisms and defines identity and composition componentwise.
-/
@[stacks 001K "product category with componentwise morphisms and composition"]
#check (prod' C D : Category.{max v₁ v₂} (C × D))

end CategoryTheory
