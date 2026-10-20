/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Symmetric

/-!
# Koszul symmetry on integer cochain complexes

@stack 0FP8
@stack 0FNI

This file installs the integer-degree sign laws and specializes the generic homological-complex
Koszul symmetry.  The construction itself is owned by
`HomologicalComplex.Koszul`.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace ComplexShape

/-- The integer Koszul sign is multiplicative in its left degree. -/
@[stacks 0FP8 "left multiplicativity of integer Koszul signs"]
theorem upInt_sigma_add_left (p q r : ℤ) :
    σ (up ℤ) (up ℤ) (up ℤ) (p + q) r =
      σ (up ℤ) (up ℤ) (up ℤ) p r * σ (up ℤ) (up ℤ) (up ℤ) q r := sorry

/-- The integer Koszul sign is multiplicative in its right degree. -/
@[stacks 0FP8 "right multiplicativity of integer Koszul signs"]
theorem upInt_sigma_add_right (p q r : ℤ) :
    σ (up ℤ) (up ℤ) (up ℤ) p (q + r) =
      σ (up ℤ) (up ℤ) (up ℤ) p q * σ (up ℤ) (up ℤ) (up ℤ) p r := sorry

/-- Integer cochain degrees carry the canonical bicharacter signs. -/
@[stacks 0FP8, stacks 0FNI "integer cochain braiding signs"]
instance upIntBraidingSigns : BraidingSigns (up ℤ) where
  sigma_add_left := upInt_sigma_add_left
  sigma_add_right := upInt_sigma_add_right

/-- The integer Koszul sign is symmetric in its two degrees. -/
@[stacks 0FP8 "symmetry of integer Koszul signs"]
theorem upInt_sigma_symm (p q : ℤ) :
    σ (up ℤ) (up ℤ) (up ℤ) q p = σ (up ℤ) (up ℤ) (up ℤ) p q := sorry

/-- Interchanging integer cochain degrees twice preserves the totalization sign. -/
@[stacks 0FP8, stacks 0FNI "integer cochain symmetric signs"]
instance upIntSymmetrySymmetry :
    TotalComplexShapeSymmetrySymmetry (up ℤ) (up ℤ) (up ℤ) where
  σ_symm := upInt_sigma_symm

end ComplexShape

namespace CochainComplex.Koszul

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasZeroObject C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

/-- The braided monoidal structure on cochain complexes whose braiding uses the Koszul sign. -/
@[stacks 0FP8, stacks 0FNI "cochain-complex braided structure", implicit_reducible]
noncomputable instance braidedCategory : BraidedCategory (CochainComplex C ℤ) where
  __ := HomologicalComplex.Koszul.braidedCategory (c := up ℤ)

/-- The symmetric monoidal structure on cochain complexes induced by the Koszul braiding. -/
@[stacks 0FP8, stacks 0FNI "cochain-complex symmetric structure", implicit_reducible]
noncomputable instance symmetricCategory : SymmetricCategory (CochainComplex C ℤ) where
  __ := HomologicalComplex.Koszul.symmetricCategory (c := up ℤ)

end CochainComplex.Koszul
