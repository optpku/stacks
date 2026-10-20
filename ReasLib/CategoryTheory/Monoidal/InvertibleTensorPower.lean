/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower

@[expose] public section

universe u v

namespace CategoryTheory.MonoidalCategory.isInvertibleObject

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Every natural tensor power of a tensor-invertible object is tensor-invertible. -/
instance tensorPower (L : C) [isInvertibleObject L] (n : ℕ) :
    isInvertibleObject (CategoryTheory.MonoidalCategory.tensorPower L n) := sorry

end CategoryTheory.MonoidalCategory.isInvertibleObject
