/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

@[expose] public section

/-!
# Extensionality for Pretriangulated Structures

A pretriangulated structure has one data-bearing field: its collection of
distinguished triangles. All remaining fields are laws, so equality of that
collection determines the whole structure.
-/

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- Two pretriangulated structures are equal when they have the same distinguished triangles. -/
@[ext]
theorem ext {P Q : Pretriangulated C}
    (h : P.distinguishedTriangles = Q.distinguishedTriangles) : P = Q := sorry

/-- A pointwise membership characterization determines a pretriangulated structure. -/
theorem ext_of_distinguished_iff {P Q : Pretriangulated C}
    (h : ∀ T : Triangle C,
      T ∈ P.distinguishedTriangles ↔ T ∈ Q.distinguishedTriangles) :
    P = Q := sorry

end CategoryTheory.Pretriangulated
