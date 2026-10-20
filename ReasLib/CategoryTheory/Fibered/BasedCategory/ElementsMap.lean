/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Based maps of categories of elements

Natural transformations of covariant functors induce strict functors between their categories of
elements, compatible with the projection to the base category.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe v u w

namespace CategoryTheory.CategoryOfElements

variable {C : Type u} [Category.{v} C]

/-- The strict based functor on categories of elements induced by a natural transformation. -/
def basedMap {U V : C ⥤ Type w} (α : U ⟶ V) :
    BasedCategory.ofFunctor (π U) ⥤ᵇ BasedCategory.ofFunctor (π V) where
  toFunctor := map α
  w := map_π α

/-- The underlying functor of `basedMap` is the category-of-elements map. -/
theorem basedMap_toFunctor {U V : C ⥤ Type w} (α : U ⟶ V) :
    (basedMap α).toFunctor = map α := sorry

end CategoryTheory.CategoryOfElements

