module

import StacksCheckRecall
import ReasLib.Algebra.Module.FiniteLength.Determinant.CoefficientField

open CategoryTheory
open scoped TensorProduct

universe u v w

/- Remark 42.68.9 (1): a finite family of finite-length modules over an equal-characteristic
local ring has a common annihilating ideal whose quotient admits a residue-field section. -/
@[stacks 0BDQ] #check
  (@Module.FiniteLengthDeterminant.CoefficientField.existsSectionForFamily :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      {ι : Type w} [Finite ι] (M : ι → ModuleCat.{v} R)
      (hM : ∀ i, IsFiniteLength R (M i))
      (hchar : ringChar R = ringChar (IsLocalRing.ResidueField R)),
      ∃ (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R),
        ∃ σ : IsLocalRing.ResidueField R →+* R ⧸ I,
          (∀ i, Module.IsTorsionBySet R (M i) I) ∧
            (Ideal.Quotient.factor hI).comp σ =
              RingHom.id (IsLocalRing.ResidueField R))

/- Remark 42.68.9 (2): restriction along the coefficient-field section makes the dimension
of each module equal to its length over the original local ring. -/
@[stacks 0BDQ] #check
  (@Module.FiniteLengthDeterminant.CoefficientField.finrank_eq_length :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
      (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
      (hAnn : Module.IsTorsionBySet R M I)
      (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
      (hσ : (Ideal.Quotient.factor hI).comp σ =
        RingHom.id (IsLocalRing.ResidueField R)),
      Module.finrank (IsLocalRing.ResidueField R)
          (Module.FiniteLengthDeterminant.CoefficientField.coefficientModule M I hAnn σ) =
        Module.FiniteLengthDeterminant.length R M hM)

/- Remark 42.68.9 (3): the determinant line is identified with the top exterior power by
the explicit coefficient-field comparison. -/
@[stacks 0BDQ] #check
  (@Module.FiniteLengthDeterminant.CoefficientField.comparisonEquiv :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      (M : ModuleCat.{v} R) (hM : IsFiniteLength R M)
      (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
      (hAnn : Module.IsTorsionBySet R M I)
      (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
      (hσ : (Ideal.Quotient.factor hI).comp σ =
        RingHom.id (IsLocalRing.ResidueField R)),
      Module.FiniteLengthDeterminant R M hM ≃ₗ[IsLocalRing.ResidueField R]
        ⋀[IsLocalRing.ResidueField R]^
          (Module.FiniteLengthDeterminant.length R M hM)
          (Module.FiniteLengthDeterminant.CoefficientField.coefficientModule M I hAnn σ))

/- Remark 42.68.9 (4): these comparisons are compatible with the determinant isomorphisms
attached to short exact sequences annihilated by the common ideal. -/
@[stacks 0BDQ] #check
  (@Module.FiniteLengthDeterminant.CoefficientField.comparison_exact :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R]
      (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R)
      (σ : IsLocalRing.ResidueField R →+* R ⧸ I)
      (hσ : (Ideal.Quotient.factor hI).comp σ =
        RingHom.id (IsLocalRing.ResidueField R))
      (S : ShortComplex (ModuleCat.{v} R))
      (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
      (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
      (hAnn₁ : Module.IsTorsionBySet R S.X₁ I)
      (hAnn₂ : Module.IsTorsionBySet R S.X₂ I)
      (hAnn₃ : Module.IsTorsionBySet R S.X₃ I)
      (e₁ : Module.FiniteLengthDeterminant.Symbol R S.X₁ h₁)
      (he₁ : Module.FiniteLengthDeterminant.symbol R S.X₁ h₁ e₁ ≠ 0)
      (e₃ : Module.FiniteLengthDeterminant.Symbol R S.X₃ h₃)
      (he₃ : Module.FiniteLengthDeterminant.symbol R S.X₃ h₃ e₃ ≠ 0),
      Module.FiniteLengthDeterminant.CoefficientField.comparisonEquiv
          S.X₂ h₂ I hI hAnn₂ σ hσ
          (Module.FiniteLengthDeterminant.exactEquiv S h₁ h₂ h₃ hS
            (Module.FiniteLengthDeterminant.symbol R S.X₁ h₁ e₁
              ⊗ₜ[IsLocalRing.ResidueField R]
                Module.FiniteLengthDeterminant.symbol R S.X₃ h₃ e₃)) =
        exteriorPower.ιMulti
          (M := Module.FiniteLengthDeterminant.CoefficientField.coefficientModule
            S.X₂ I hAnn₂ σ)
          (IsLocalRing.ResidueField R)
          (Module.FiniteLengthDeterminant.length R S.X₂ h₂)
          (Module.FiniteLengthDeterminant.exactSequence S h₁ h₂ h₃ e₁ e₃ :
            Fin (Module.FiniteLengthDeterminant.length R S.X₂ h₂) →
              Module.FiniteLengthDeterminant.CoefficientField.coefficientModule
                S.X₂ I hAnn₂ σ))
