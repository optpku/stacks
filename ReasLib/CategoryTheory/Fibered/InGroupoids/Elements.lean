/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Category-of-elements cofiberedness

The projection from the category of elements of a covariant type-valued functor is cofibered in
groupoids after passage to opposites.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.CategoryOfElements

variable {C : Type u} [Category.{v} C]

/-- The opposite of the category-of-elements projection is fibred in groupoids. -/
instance instIsFiberedInGroupoidsOp (F : C ⥤ Type w) :
    Functor.IsFibered.InGroupoids (π F).op := sorry

end CategoryTheory.CategoryOfElements
