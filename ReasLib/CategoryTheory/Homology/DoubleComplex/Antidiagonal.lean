/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Componentwise maps on antidiagonals

A family of maps between corresponding bidegrees induces a map between any fixed total-degree
objects.  No compatibility with either differential is required.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w₁ w₂ w₁₂

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I₁ : Type w₁} {I₂ : Type w₂} {I₁₂ : Type w₁₂}
variable {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
variable [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
variable {K L : HomologicalComplex₂ C c₁ c₂} [K.HasTotal c₁₂] [L.HasTotal c₁₂]

/-- Assemble maps in corresponding bidegrees into a map on one total-degree object. -/
@[stacks 0130 "componentwise map on a total-complex antidiagonal"]
noncomputable def antidiagonalMap
    (f : ∀ i₁ i₂, (K.X i₁).X i₂ ⟶ (L.X i₁).X i₂) (n : I₁₂) :
    (K.total c₁₂).X n ⟶ (L.total c₁₂).X n :=
  K.totalDesc fun i₁ i₂ h ↦ f i₁ i₂ ≫ L.ιTotal c₁₂ i₁ i₂ n h

/-- Restricting `antidiagonalMap` to a summand recovers the corresponding component followed by
the target summand inclusion. -/
@[stacks 0130 "antidiagonal map on a total-complex summand", reassoc (attr := simp)]
theorem ιTotal_antidiagonalMap
    (f : ∀ i₁ i₂, (K.X i₁).X i₂ ⟶ (L.X i₁).X i₂)
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂)
    (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    K.ιTotal c₁₂ i₁ i₂ n h ≫ antidiagonalMap f n =
      f i₁ i₂ ≫ L.ιTotal c₁₂ i₁ i₂ n h := sorry

end HomologicalComplex₂
