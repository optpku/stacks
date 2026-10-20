/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Invertible mates along bicategorical equivalences

This leaf owns the invertible mate of an invertible square transported across
two bicategorical equivalences.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B]

namespace Bicategory.Equivalence

variable {a b c d : B} {g : a ⟶ c} {h : b ⟶ d}

/-- The mate of an invertible square along bicategorical equivalences is invertible.

For general adjunctions, taking a mate need not preserve invertibility. The inverse here is
obtained by taking the mate of the inverse square along the reversed equivalences. -/
theorem mateIso.hom_inv_id (e₁ : a ≌ b) (e₂ : c ≌ d)
    (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    Bicategory.mateEquiv e₁.toAdjunction e₂.toAdjunction α.hom ≫
        (Bicategory.mateEquiv e₁.symm.toAdjunction
          e₂.symm.toAdjunction).symm α.inv =
      𝟙 (e₁.inv ≫ g) := sorry

/-- The mate of an invertible square and the mate of its inverse cancel in the reverse
order. -/
theorem mateIso.inv_hom_id (e₁ : a ≌ b) (e₂ : c ≌ d)
    (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (Bicategory.mateEquiv e₁.symm.toAdjunction
          e₂.symm.toAdjunction).symm α.inv ≫
        Bicategory.mateEquiv e₁.toAdjunction e₂.toAdjunction α.hom =
      𝟙 (h ≫ e₂.inv) := sorry

/-- Transfer an invertible square across two bicategorical equivalences.

Given `α : g ≫ e₂.hom ≅ e₁.hom ≫ h`, this is the canonical invertible mate
`e₁.inv ≫ g ≅ h ≫ e₂.inv`. -/
@[stacks 0040 "invertible mates along bicategorical equivalences"]
def mateIso (e₁ : a ≌ b) (e₂ : c ≌ d)
    (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    e₁.inv ≫ g ≅ h ≫ e₂.inv where
  hom := Bicategory.mateEquiv e₁.toAdjunction e₂.toAdjunction α.hom
  inv := (Bicategory.mateEquiv e₁.symm.toAdjunction
    e₂.symm.toAdjunction).symm α.inv
  hom_inv_id := mateIso.hom_inv_id e₁ e₂ α
  inv_hom_id := mateIso.inv_hom_id e₁ e₂ α

/-- The forward cell of `mateIso` is the ordinary mate of the forward square. -/
@[simp]
theorem mateIso.hom (e₁ : a ≌ b) (e₂ : c ≌ d)
    (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (mateIso e₁ e₂ α).hom =
      Bicategory.mateEquiv e₁.toAdjunction e₂.toAdjunction α.hom := sorry

/-- The inverse cell of `mateIso` is the inverse-direction mate of the inverse square. -/
@[simp]
theorem mateIso.inv (e₁ : a ≌ b) (e₂ : c ≌ d)
    (α : g ≫ e₂.hom ≅ e₁.hom ≫ h) :
    (mateIso e₁ e₂ α).inv =
      (Bicategory.mateEquiv e₁.symm.toAdjunction
        e₂.symm.toAdjunction).symm α.inv := sorry

end Bicategory.Equivalence

end CategoryTheory
