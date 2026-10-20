/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of costructured arrows

This file gives the reusable Hom API for `CostructuredArrow`, dual to the corresponding
`StructuredArrow` API. A morphism is identified with its left component together with the
defining triangle. When the target structure map is an isomorphism, a second interface rewrites
the triangle using its inverse.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory.CostructuredArrow

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {S : C ⥤ D} {T : D}

/-- A left-component map lifts to a costructured-arrow morphism exactly when its defining
triangle commutes. -/
theorem exists_hom_left_iff
    (A B : CostructuredArrow S T) (g : A.left ⟶ B.left) :
    (∃ f : A ⟶ B, f.left = g) ↔ S.map g ≫ B.hom = A.hom := sorry

/-- The left component of a costructured-arrow morphism satisfies the defining triangle. -/
theorem homEquiv.condition
    (A B : CostructuredArrow S T) (f : A ⟶ B) :
    S.map f.left ≫ B.hom = A.hom := sorry

/-- Reconstructing a costructured-arrow morphism from its left component recovers the original
morphism. -/
theorem homEquiv.leftInverse
    (A B : CostructuredArrow S T) (f : A ⟶ B) :
    CostructuredArrow.homMk f.left (homEquiv.condition A B f) = f := sorry

/-- Reconstructing and then projecting a compatible left component recovers the original
subtype element. -/
theorem homEquiv.rightInverse
    (A B : CostructuredArrow S T)
    (g : {g : A.left ⟶ B.left // S.map g ≫ B.hom = A.hom}) :
    (⟨(CostructuredArrow.homMk g.1 g.2).left,
        homEquiv.condition A B (CostructuredArrow.homMk g.1 g.2)⟩ :
      {h : A.left ⟶ B.left // S.map h ≫ B.hom = A.hom}) = g := sorry

/-- Costructured-arrow morphisms are canonically equivalent to left-component maps satisfying
the defining triangle. This is the intrinsic Hom interface; it requires no invertibility
assumption. -/
@[stacks 02Y5 "(2) intrinsic costructured-arrow Hom equivalence"]
def homEquiv (A B : CostructuredArrow S T) :
    (A ⟶ B) ≃ {g : A.left ⟶ B.left // S.map g ≫ B.hom = A.hom} where
  toFun f := ⟨f.left, homEquiv.condition A B f⟩
  invFun g := CostructuredArrow.homMk g.1 g.2
  left_inv := homEquiv.leftInverse A B
  right_inv := homEquiv.rightInverse A B

/-- The intrinsic Hom equivalence sends a costructured-arrow morphism to its left component. -/
@[simp]
theorem homEquiv.apply_val
    (A B : CostructuredArrow S T) (f : A ⟶ B) :
    ((homEquiv A B) f).1 = f.left := sorry

/-- The inverse intrinsic Hom equivalence has the supplied compatible map as left component. -/
@[simp]
theorem homEquiv.symm_apply_left
    (A B : CostructuredArrow S T)
    (g : {g : A.left ⟶ B.left // S.map g ≫ B.hom = A.hom}) :
    ((homEquiv A B).symm g).left = g.1 := sorry

noncomputable section

/-- If the target structure map is invertible, the defining triangle is equivalent to the
inverse-form equation for the left component. -/
theorem comp_eq_iff_map_eq
    (A B : CostructuredArrow S T) [IsIso B.hom]
    (g : A.left ⟶ B.left) :
    S.map g ≫ B.hom = A.hom ↔ S.map g = A.hom ≫ (asIso B.hom).inv := sorry

/-- Construct a costructured-arrow morphism from an inverse-form equation for its left component.
Only the target structure map must be invertible. -/
@[stacks 02Y5 "(2) formal dual reusable costructured-arrow morphism constructor"]
def homMkInv
    (A B : CostructuredArrow S T) [IsIso B.hom]
    (g : A.left ⟶ B.left)
    (h : S.map g = A.hom ≫ (asIso B.hom).inv) : A ⟶ B :=
  CostructuredArrow.homMk g ((comp_eq_iff_map_eq A B g).mpr h)

/-- The left component of `homMkInv` is the supplied morphism. -/
@[simp]
theorem homMkInv_left
    (A B : CostructuredArrow S T) [IsIso B.hom]
    (g : A.left ⟶ B.left)
    (h : S.map g = A.hom ≫ (asIso B.hom).inv) :
    (homMkInv A B g h).left = g := sorry

/-- The left component of a costructured-arrow morphism satisfies the inverse-form equation when
the target structure map is invertible. -/
theorem homEquivInv.condition
    (A B : CostructuredArrow S T) [IsIso B.hom] (f : A ⟶ B) :
    S.map f.left = A.hom ≫ (asIso B.hom).inv := sorry

/-- Reconstructing a costructured-arrow morphism through the inverse-form interface recovers the
original morphism. -/
theorem homEquivInv.leftInverse
    (A B : CostructuredArrow S T) [IsIso B.hom] (f : A ⟶ B) :
    homMkInv A B f.left (homEquivInv.condition A B f) = f := sorry

/-- Projecting a morphism reconstructed from inverse-form data recovers the original subtype
element. -/
theorem homEquivInv.rightInverse
    (A B : CostructuredArrow S T) [IsIso B.hom]
    (g : {g : A.left ⟶ B.left // S.map g = A.hom ≫ (asIso B.hom).inv}) :
    (⟨(homMkInv A B g.1 g.2).left,
        homEquivInv.condition A B (homMkInv A B g.1 g.2)⟩ :
      {h : A.left ⟶ B.left // S.map h = A.hom ≫ (asIso B.hom).inv}) = g := sorry

/-- Formal dual of Lemma 4.42.1 (Stacks 02Y5) (2): costructured-arrow morphisms are canonically
equivalent to left-component maps satisfying the inverse-form equation when the target structure
map is invertible. -/
@[stacks 02Y5 "(2) formal dual costructured-arrow Hom equivalence"]
def homEquivInv
    (A B : CostructuredArrow S T) [IsIso B.hom] :
    (A ⟶ B) ≃
      {g : A.left ⟶ B.left // S.map g = A.hom ≫ (asIso B.hom).inv} where
  toFun f := ⟨f.left, homEquivInv.condition A B f⟩
  invFun g := homMkInv A B g.1 g.2
  left_inv := homEquivInv.leftInverse A B
  right_inv := homEquivInv.rightInverse A B

/-- The inverse-form Hom equivalence sends a costructured-arrow morphism to its left component. -/
@[simp]
theorem homEquivInv.apply_val
    (A B : CostructuredArrow S T) [IsIso B.hom] (f : A ⟶ B) :
    ((homEquivInv A B) f).1 = f.left := sorry

/-- The inverse of the inverse-form Hom equivalence has the supplied map as left component. -/
@[simp]
theorem homEquivInv.symm_apply_left
    (A B : CostructuredArrow S T) [IsIso B.hom]
    (g : {g : A.left ⟶ B.left // S.map g = A.hom ≫ (asIso B.hom).inv}) :
    ((homEquivInv A B).symm g).left = g.1 := sorry

end

end CategoryTheory.CostructuredArrow

/- Axiom audit: `homEquiv`, `homMkInv`, and `homEquivInv` retain their supplied left-component
maps as explicit non-Prop data. Any statement-stage `sorryAx` reported below is confined to the
Prop-valued triangle and inverse-law fields. -/
