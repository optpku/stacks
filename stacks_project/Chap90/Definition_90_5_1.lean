/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]
variable (p : F ⥤ C)

/- Definition 90.5.1: a functor `p : F ⥤ C` is a category cofibered in groupoids over `C`
precisely when `p.op : Fᵒᵖ ⥤ Cᵒᵖ` is a category fibred in groupoids over `Cᵒᵖ`. -/
@[stacks 06GJ]
#check (CategoryTheory.Functor.IsFibered.InGroupoids p.op : Prop)
