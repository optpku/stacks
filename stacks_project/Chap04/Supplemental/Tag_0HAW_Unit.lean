/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Unit

@[expose] public section

universe v u

#check (CategoryTheory.SemigroupalCategory.UnitSeed.ofUnit :
  ∀ {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.SemigroupalCategory C],
    CategoryTheory.SemigroupalCategory.Unit C → CategoryTheory.SemigroupalCategory.UnitSeed C)
