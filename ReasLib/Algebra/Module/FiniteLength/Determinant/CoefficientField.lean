/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ExteriorPower
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Restriction
public import ReasLib.RingTheory.Completion.CoefficientRing
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.LocalRing.ResidueField.Quotient

/-!
# Coefficient-field comparisons for finite-length determinants

This file constructs a common coefficient-field section for a finite family of
finite-length modules and compares the resulting determinant lines with top exterior powers.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Module.FiniteLengthDeterminant.CoefficientField

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A finite family of finite-length modules over an equal-characteristic local ring has a
common annihilating ideal below the maximal ideal whose quotient admits a residue-field
section. -/
theorem existsSectionForFamily {ι : Type w} [Finite ι]
    (M : ι → ModuleCat.{v} R) (hM : ∀ i, IsFiniteLength R (M i))
    (hchar : ringChar R = ringChar (IsLocalRing.ResidueField R)) :
    ∃ (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R),
      ∃ σ : IsLocalRing.ResidueField R →+* R ⧸ I,
        (∀ i, Module.IsTorsionBySet R (M i) I) ∧
          (Ideal.Quotient.factor hI).comp σ =
            RingHom.id (IsLocalRing.ResidueField R) := sorry

/-- The module over a quotient ring induced by an ideal that annihilates the original
module. -/
def quotientModule (M : ModuleCat.{v} R) (I : Ideal R)
    (hAnn : Module.IsTorsionBySet R M I) : ModuleCat.{v} (R ⧸ I) :=
  @ModuleCat.of (R ⧸ I) inferInstance M inferInstance hAnn.module

/-- Finite length descends to the quotient action supplied by an annihilating ideal. -/
theorem isFiniteLengthQuotient (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hAnn : Module.IsTorsionBySet R M I) :
    IsFiniteLength (R ⧸ I) (quotientModule M I hAnn) := sorry

/-- Restricting the quotient-module action along a chosen residue-field section gives a
bundled vector space over the residue field. -/
def coefficientModule (M : ModuleCat.{v} R) (I : Ideal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I) :
    ModuleCat.{v} (IsLocalRing.ResidueField R) :=
  (ModuleCat.restrictScalars σ).obj (quotientModule M I hAnn)

/-- A coefficient-field section of a local quotient induces a bijection on residue fields. -/
theorem sectionResidue_bijective (I : Ideal R)
    (hI : I ≤ IsLocalRing.maximalIdeal R)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    -- Local instance justification (proof-local temporary data): the residue-field map requires the quotient local-ring structure determined by `hI`.
    letI : IsLocalRing (R ⧸ I) := IsLocalRing.quotient_of_le_maximalIdeal I hI
    Function.Bijective (IsLocalRing.ResidueField.map σ) := sorry

/-- The dimension of the vector space obtained from a finite-length module through a
coefficient-field section equals its length over the original local ring. -/
theorem finrank_eq_length (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    Module.finrank (IsLocalRing.ResidueField R) (coefficientModule M I hAnn σ) =
      length R M hM := sorry

/-- The free-symbol map sends an admissible determinant family to its wedge under the
explicit coefficient-field action. -/
def comparisonFree (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I) :
    Free R M hM →ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(length R M hM) (coefficientModule M I hAnn σ) :=
  Finsupp.linearCombination (IsLocalRing.ResidueField R) fun e : Symbol R M hM ↦
    exteriorPower.ιMulti (IsLocalRing.ResidueField R) (length R M hM) e.1

/-- The coefficient-section wedge map kills the defining determinant relations. -/
theorem comparisonFree_relation (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    ∀ x, Relation R M hM x → comparisonFree M hM I hAnn σ x = 0 := sorry

/-- The coefficient-field comparison map from a finite-length determinant line to the
corresponding top exterior power. -/
def comparison (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hrel : ∀ x, Relation R M hM x → comparisonFree M hM I hAnn σ x = 0) :
    Module.FiniteLengthDeterminant R M hM →ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(length R M hM) (coefficientModule M I hAnn σ) :=
  lift R M hM (comparisonFree M hM I hAnn σ) hrel

/-- The coefficient-field comparison map is bijective. -/
theorem comparison_bijective (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    Function.Bijective
      (comparison M hM I hAnn σ (comparisonFree_relation M hM I hI hAnn σ hσ)) := sorry

/-- The inverse function of the coefficient-field comparison is a left inverse. -/
theorem comparison_invFun_left (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    Function.LeftInverse
      (Function.invFun
        (comparison M hM I hAnn σ (comparisonFree_relation M hM I hI hAnn σ hσ)))
      (comparison M hM I hAnn σ
        (comparisonFree_relation M hM I hI hAnn σ hσ)) := sorry

/-- The inverse function of the coefficient-field comparison is a right inverse. -/
theorem comparison_invFun_right (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    Function.RightInverse
      (Function.invFun
        (comparison M hM I hAnn σ (comparisonFree_relation M hM I hI hAnn σ hσ)))
      (comparison M hM I hAnn σ
        (comparisonFree_relation M hM I hI hAnn σ hσ)) := sorry

/-- The determinant line of a finite-length module is linearly equivalent to the top exterior
power of its vector space obtained from a coefficient-field section. -/
def comparisonEquiv (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
    (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hAnn : Module.IsTorsionBySet R M I)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R)) :
    Module.FiniteLengthDeterminant R M hM ≃ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(length R M hM) (coefficientModule M I hAnn σ) :=
  { comparison M hM I hAnn σ (comparisonFree_relation M hM I hI hAnn σ hσ) with
    invFun := Function.invFun
      (comparison M hM I hAnn σ (comparisonFree_relation M hM I hI hAnn σ hσ))
    left_inv := comparison_invFun_left M hM I hI hAnn σ hσ
    right_inv := comparison_invFun_right M hM I hI hAnn σ hσ }

/-- The coefficient-field comparison carries the short-exact determinant equivalence on
nonzero symbols to the usual concatenated top wedge. -/
theorem comparison_exact (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
    (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
    (hσ : (Ideal.Quotient.factor hI).comp σ =
      RingHom.id (IsLocalRing.ResidueField R))
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (hAnn₁ : Module.IsTorsionBySet R S.X₁ I)
    (hAnn₂ : Module.IsTorsionBySet R S.X₂ I)
    (hAnn₃ : Module.IsTorsionBySet R S.X₃ I)
    (e₁ : Symbol R S.X₁ h₁) (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0)
    (e₃ : Symbol R S.X₃ h₃) (he₃ : symbol R S.X₃ h₃ e₃ ≠ 0) :
    comparisonEquiv S.X₂ h₂ I hI hAnn₂ σ hσ
        (exactEquiv S h₁ h₂ h₃ hS
          (symbol R S.X₁ h₁ e₁ ⊗ₜ[IsLocalRing.ResidueField R]
            symbol R S.X₃ h₃ e₃)) =
      exteriorPower.ιMulti (M := coefficientModule S.X₂ I hAnn₂ σ)
        (IsLocalRing.ResidueField R) (length R S.X₂ h₂)
        (exactSequence S h₁ h₂ h₃ e₁ e₃ :
          Fin (length R S.X₂ h₂) → coefficientModule S.X₂ I hAnn₂ σ) := sorry

end Module.FiniteLengthDeterminant.CoefficientField
