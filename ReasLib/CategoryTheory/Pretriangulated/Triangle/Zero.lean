/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Zero Cones of Distinguished Triangles

This leaf records the fixed-morphism forms of the standard relation between an
isomorphism and a distinguished triangle with zero third object.  It does not
choose a cone, so it remains usable in any pretriangulated category.
-/

namespace CategoryTheory.Pretriangulated

open Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]

/-- Stacks 05QR, Lemma 13.4.9 (1): a morphism is an isomorphism exactly when every
distinguished completion has a zero third object. -/
@[stacks 05QR]
theorem isIso_iff_forall_isZero_obj₃_of_distinguished {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔
      ∀ ⦃Z : C⦄ ⦃g : Y ⟶ Z⦄ ⦃h : Z ⟶ X⟦(1 : ℤ)⟧⦄
        (_ : Triangle.mk f g h ∈ distTriang C), Limits.IsZero Z := sorry

/-- Stacks 05QR, Lemma 13.4.9 (2): a morphism is an isomorphism exactly when its
zero-cone triangle is distinguished. -/
@[stacks 05QR]
theorem isIso_iff_zeroCone_distinguished {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ Triangle.mk f (0 : Y ⟶ 0) 0 ∈ distTriang C := sorry

end CategoryTheory.Pretriangulated
