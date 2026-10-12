/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Koszul symmetry on nonnegative chain complexes

This file supplies the concrete interchange sign for `ComplexShape.down ℕ` and specializes the
generic `HomologicalComplex.Koszul` symmetry to chain complexes.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace ComplexShape

/-- Swapping the two nonnegative totalization degrees preserves their sum. -/
theorem downNat_pi_symm (p q : ℕ) :
    π (down ℕ) (down ℕ) (down ℕ) ⟨q, p⟩ =
      π (down ℕ) (down ℕ) (down ℕ) ⟨p, q⟩ := sorry

/-- The sign `(-1)^(p*q)` intertwines a differential in the left chain degree. -/
theorem downNat_sigma_epsilon_left {p p' : ℕ} (h : (down ℕ).Rel p p') (q : ℕ) :
    (-1 : ℤˣ) ^ (p * q) * ε₁ (down ℕ) (down ℕ) (down ℕ) ⟨p, q⟩ =
      ε₂ (down ℕ) (down ℕ) (down ℕ) ⟨q, p⟩ * (-1 : ℤˣ) ^ (p' * q) := sorry

/-- The sign `(-1)^(p*q)` intertwines a differential in the right chain degree. -/
theorem downNat_sigma_epsilon_right (p : ℕ) {q q' : ℕ} (h : (down ℕ).Rel q q') :
    (-1 : ℤˣ) ^ (p * q) * ε₂ (down ℕ) (down ℕ) (down ℕ) ⟨p, q⟩ =
      ε₁ (down ℕ) (down ℕ) (down ℕ) ⟨q, p⟩ * (-1 : ℤˣ) ^ (p * q') := sorry

/-- The totalization of nonnegative chain bicomplexes uses the interchange sign `(-1)^(p*q)`. -/
@[stacks 0FP8 "nonnegative chain interchange signs"]
instance downNatTotalSymmetry :
    TotalComplexShapeSymmetry (down ℕ) (down ℕ) (down ℕ) where
  symm := downNat_pi_symm
  σ p q := (-1 : ℤˣ) ^ (p * q)
  σ_ε₁ := downNat_sigma_epsilon_left
  σ_ε₂ := downNat_sigma_epsilon_right

/-- The nonnegative-chain interchange sign is multiplicative in its left degree. -/
theorem downNat_sigma_add_left (p q r : ℕ) :
    σ (down ℕ) (down ℕ) (down ℕ) (p + q) r =
      σ (down ℕ) (down ℕ) (down ℕ) p r * σ (down ℕ) (down ℕ) (down ℕ) q r := sorry

/-- The nonnegative-chain interchange sign is multiplicative in its right degree. -/
theorem downNat_sigma_add_right (p q r : ℕ) :
    σ (down ℕ) (down ℕ) (down ℕ) p (q + r) =
      σ (down ℕ) (down ℕ) (down ℕ) p q * σ (down ℕ) (down ℕ) (down ℕ) p r := sorry

/-- Nonnegative chain degrees carry the canonical bicharacter signs. -/
@[stacks 0FP8 "nonnegative chain braiding signs"]
instance downNatBraidingSigns : BraidingSigns (down ℕ) where
  sigma_add_left := downNat_sigma_add_left
  sigma_add_right := downNat_sigma_add_right

/-- The nonnegative-chain interchange sign is symmetric in its two degrees. -/
theorem downNat_sigma_symm (p q : ℕ) :
    σ (down ℕ) (down ℕ) (down ℕ) q p =
      σ (down ℕ) (down ℕ) (down ℕ) p q := sorry

/-- Interchanging nonnegative chain degrees twice preserves the totalization sign. -/
@[stacks 0FP8 "nonnegative chain symmetric signs"]
instance downNatSymmetrySymmetry :
    TotalComplexShapeSymmetrySymmetry (down ℕ) (down ℕ) (down ℕ) where
  σ_symm := downNat_sigma_symm

end ComplexShape

namespace ChainComplex.Koszul

variable {C : Type u} [Category.{v} C] [Preadditive C] [CategoryTheory.Limits.HasZeroObject C]
variable [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
variable [∀ G₁ G₂ : GradedObject ℕ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℕ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℕ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℕ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]

/-- The braided monoidal structure on nonnegative chain complexes with the Koszul sign. -/
@[stacks 0FP8 "nonnegative chain-complex braided structure", implicit_reducible]
noncomputable instance braidedCategory : BraidedCategory (ChainComplex C ℕ) where
  __ := HomologicalComplex.Koszul.braidedCategory (c := down ℕ)

/-- The symmetric monoidal structure on nonnegative chain complexes with the Koszul sign. -/
@[stacks 0FP8 "nonnegative chain-complex symmetric structure", implicit_reducible]
noncomputable instance symmetricCategory : SymmetricCategory (ChainComplex C ℕ) where
  __ := HomologicalComplex.Koszul.symmetricCategory (c := down ℕ)

end ChainComplex.Koszul

