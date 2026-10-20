/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import ReasLib.CategoryTheory.Monoidal.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coproducts of flat objects

This file names the exact closure condition needed when tensor products of graded objects are
formed by small coproducts. It is independent of any module or sheaf presentation.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.MonoidalCategory.IsFlat

/-- Flat objects are closed under the `Type`-indexed coproducts that exist in `C`. -/
@[stacks 03EU "flat-object coproduct closure"]
class Coproducts (C : Type u) [Category.{v} C] [MonoidalCategory C] : Prop where
  /-- A coproduct of flat objects is flat. -/
  isFlat {I : Type} (F : I → C) [HasCoproduct F]
    (hF : ∀ i, MonoidalCategory.IsFlat (F i)) :
    MonoidalCategory.IsFlat (∐ F)

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A small coproduct of flat objects is flat whenever flat objects in `C` have coproduct
closure. -/
theorem coproduct [Coproducts C] {I : Type} (F : I → C) [HasCoproduct F]
    (hF : ∀ i, MonoidalCategory.IsFlat (F i)) :
    MonoidalCategory.IsFlat (∐ F) := sorry

end CategoryTheory.MonoidalCategory.IsFlat
