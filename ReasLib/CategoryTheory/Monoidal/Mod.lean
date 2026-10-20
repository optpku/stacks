/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Mod

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The action of a monoid object is compatible with multiplication and the unit. -/
theorem laws (M X : C) [MonObj M] (A : ModObj M X) :
    (μ[M] ▷ X) ≫ A.smul = (α_ M M X).hom ≫ (M ◁ A.smul) ≫ A.smul ∧
      (η[M] ▷ X) ≫ A.smul = (λ_ X).hom := sorry

end CategoryTheory.ModObj
