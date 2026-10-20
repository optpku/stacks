/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.NatTrans
import StacksCheckRecall

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (F G : C ⥤ D)

/-
Definition 4.2.15: a natural transformation, or morphism of functors, between functors
`F G : C ⥤ D` is the canonical structure `NatTrans F G`. Its components are the morphisms
`t.app X : F.obj X ⟶ G.obj X`, and `t.naturality f` says that every naturality square commutes.
-/
@[stacks 001I "natural transformations by components and commuting naturality squares"]
#check (NatTrans F G : Type max u₁ v₂)

end CategoryTheory
