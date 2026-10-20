/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal-preadditive functor categories

The pointwise monoidal structure on a functor category preserves additivity in
each tensor variable.  This is a structural fact about the target category,
independent of the indexing category.
-/

@[expose] public section

universe vJ vC uJ uC

namespace CategoryTheory.Monoidal.FunctorCategory

variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C] [Preadditive C] [MonoidalCategory C]

/-- Pointwise tensor product makes `J ⥤ C` monoidal-preadditive whenever `C` is
monoidal-preadditive. -/
instance monoidalPreadditive [MonoidalPreadditive C] :
    MonoidalPreadditive (J ⥤ C) := sorry

end CategoryTheory.Monoidal.FunctorCategory
