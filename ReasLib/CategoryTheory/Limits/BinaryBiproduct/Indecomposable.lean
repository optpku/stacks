/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

open CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- An object is indecomposable exactly when it is nonzero and every binary biproduct
decomposition has a zero summand. -/
public theorem indecomposable_iff (X : C) :
    Indecomposable X ↔ ¬ IsZero X ∧ ∀ Y Z, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z := Iff.rfl

end CategoryTheory
