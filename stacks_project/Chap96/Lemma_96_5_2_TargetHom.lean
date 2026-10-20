/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.TargetYoneda

@[expose] public section

open CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u v

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids C}

#check (CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable.iff_targetYoneda :
    ∀ (F : X ⟶ Y), relativelyRepresentable F ↔ targetYoneda.representable F)
