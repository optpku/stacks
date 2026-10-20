/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.Naturality
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ThreeByThree
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ExteriorPower

/-!
# Coherence of finite-length determinant lines

Compatibility bridge for exact-sequence naturality, signed three-by-three coherence, and the
residue-vector-space comparison.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Naturality of the exact-sequence determinant equivalence has the expected type. -/
#check (exactEquiv_naturality :
  {S T : ShortComplex (ModuleCat.{v} R)} →
    (hS₁ : IsFiniteLength R S.X₁) → (hS₂ : IsFiniteLength R S.X₂) →
    (hS₃ : IsFiniteLength R S.X₃) → (hT₁ : IsFiniteLength R T.X₁) →
    (hT₂ : IsFiniteLength R T.X₂) → (hT₃ : IsFiniteLength R T.X₃) →
    (hS : S.ShortExact) → (e : S ≅ T) →
    (exactEquiv T hT₁ hT₂ hT₃ (ShortComplex.shortExact_of_iso e hS)).toLinearMap.comp
        (TensorProduct.congr
          (mapEquiv hS₁ hT₁ (ShortComplex.π₁.mapIso e).toLinearEquiv)
          (mapEquiv hS₃ hT₃ (ShortComplex.π₃.mapIso e).toLinearEquiv)).toLinearMap =
      (mapEquiv hS₂ hT₂ (ShortComplex.π₂.mapIso e).toLinearEquiv).toLinearMap.comp
        (exactEquiv S hS₁ hS₂ hS₃ hS).toLinearMap)

/- Signed three-by-three coherence has the expected type. -/
#check (ThreeByThree.commutes :
  (D : ThreeByThree.{u, v} R) → ThreeByThree.viaRows D = ThreeByThree.viaColumns D)

/- Compatibility with the top exterior power has the expected type. -/
#check (exactEquiv_toExteriorPower_tmul_symbol :
  (S : ShortComplex (ModuleCat.{v} R)) →
    (h₁ : IsFiniteLength R S.X₁) → (h₂ : IsFiniteLength R S.X₂) →
    (h₃ : IsFiniteLength R S.X₃) → (hS : S.ShortExact) →
    (hAnn₁ : Module.IsTorsionBySet R S.X₁ (IsLocalRing.maximalIdeal R)) →
    (hAnn₂ : Module.IsTorsionBySet R S.X₂ (IsLocalRing.maximalIdeal R)) →
    (hAnn₃ : Module.IsTorsionBySet R S.X₃ (IsLocalRing.maximalIdeal R)) →
    (e₁ : Symbol R S.X₁ h₁) → (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0) →
    (e₃ : Symbol R S.X₃ h₃) → (he₃ : symbol R S.X₃ h₃ e₃ ≠ 0) →
    -- Local instance justification (search instability): `hAnn₂` uniquely supplies the residue-field module action, but inference cannot recover it.
    letI : Module (IsLocalRing.ResidueField R) S.X₂ := hAnn₂.module
    toExteriorPower R S.X₂ h₂ hAnn₂ (length_eq_finrank R S.X₂ h₂ hAnn₂)
        (exactEquiv S h₁ h₂ h₃ hS
          (symbol R S.X₁ h₁ e₁ ⊗ₜ[IsLocalRing.ResidueField R] symbol R S.X₃ h₃ e₃)) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R)
        (Module.finrank (IsLocalRing.ResidueField R) S.X₂)
        (exactSequence S h₁ h₂ h₃ e₁ e₃ ∘
          Fin.cast (length_eq_finrank R S.X₂ h₂ hAnn₂).symm))

end Module.FiniteLengthDeterminant
