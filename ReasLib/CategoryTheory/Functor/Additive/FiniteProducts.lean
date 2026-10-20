/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable [Preadditive C] [Preadditive D]

/-- An additive functor between preadditive categories preserves finite products
and sends every zero object to a zero object. -/
theorem preservesFiniteProducts_and_map_isZero (F : C ⥤ D) [F.Additive] :
    Limits.PreservesFiniteProducts F ∧
      (∀ {X : C}, Limits.IsZero X → Limits.IsZero (F.obj X)) :=
  ⟨preservesFiniteProductsOfAdditive F, map_isZero F⟩

end CategoryTheory.Functor
