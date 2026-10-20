/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

@[expose] public section

open CategoryTheory

namespace CategoryTheory.PresheafSlice

universe u v w

/-- The Cartesian monoidal structure on the slice of a Type-valued functor. -/
noncomputable instance cartesianMonoidalCategory {J : Type u} [Category.{v} J]
    (F : J ⥤ Type w) : CartesianMonoidalCategory (Over F) :=
  Over.cartesianMonoidalCategory F

/-- The canonical Cartesian braiding on the slice of a Type-valued functor. -/
noncomputable instance braidedCategory {J : Type u} [Category.{v} J]
    (F : J ⥤ Type w) : BraidedCategory (Over F) :=
  Over.braidedCategory F

end CategoryTheory.PresheafSlice
