/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Invariant
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Tensor

@[expose] public section

/-!
# Pro-Invariance of Tensor-Derived-Limit Functors

@stack 091L

This leaf combines preservation of stagewise pro-isomorphisms by a fixed
tensor factor with their inversion by total derived inverse limit.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit

variable {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]
variable [MonoidalPreadditive (SequentialInverseSystem A)]
variable [∀ (K L : CochainComplex (SequentialInverseSystem A) ℤ),
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (SequentialInverseSystem A)) (up ℤ)]
variable [HasLimitsOfShape ℕᵒᵖ A]
variable [(lim : SequentialInverseSystem A ⥤ A).Additive]
variable [HasDerivedFunctor A]

/-- Stacks 091L: a stagewise pro-isomorphism remains an isomorphism after
fixed-left derived tensoring and total right derived inverse limit, provided
the two constituent functors preserve and invert the relevant property. -/
@[stacks 091L]
theorem tensorLeft_map_isIso
    (K : DerivedCategory A)
    [DerivedCategory.DerivedTensor.Left.Has (C := SequentialInverseSystem A)]
    [(Pro.isomorphisms A).IsPreservedBy (tensorLeftFactor K)]
    [Pro.Invariant A] {E D : DerivedCategory (SequentialInverseSystem A)}
    (φ : E ⟶ D) (hφ : Pro.isomorphisms A φ) :
    IsIso ((tensorLeft K).map φ) := sorry

end CategoryTheory.DerivedLimit
