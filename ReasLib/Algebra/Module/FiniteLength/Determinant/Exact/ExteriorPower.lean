/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Module.FiniteLength.Determinant.ExteriorPower

/-!
# Exact-sequence determinants and top exterior powers

For modules annihilated by the maximal ideal, the short-exact determinant equivalence agrees
on symbol generators with concatenation in the top exterior power over the residue field.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- For a short exact sequence of residue-field vector spaces, the finite-length determinant
equivalence sends nonzero symbol generators to the usual concatenated top wedge. -/
theorem exactEquiv_toExteriorPower_tmul_symbol
    (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (hAnn₁ : Module.IsTorsionBySet R S.X₁ (IsLocalRing.maximalIdeal R))
    (hAnn₂ : Module.IsTorsionBySet R S.X₂ (IsLocalRing.maximalIdeal R))
    (hAnn₃ : Module.IsTorsionBySet R S.X₃ (IsLocalRing.maximalIdeal R))
    (e₁ : Symbol R S.X₁ h₁) (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0)
    (e₃ : Symbol R S.X₃ h₃) (he₃ : symbol R S.X₃ h₃ e₃ ≠ 0) :
    -- Local instance justification (search instability): `hAnn₂` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) S.X₂ := hAnn₂.module
    toExteriorPower R S.X₂ h₂ hAnn₂ (length_eq_finrank R S.X₂ h₂ hAnn₂)
        (exactEquiv S h₁ h₂ h₃ hS
          (symbol R S.X₁ h₁ e₁ ⊗ₜ[IsLocalRing.ResidueField R] symbol R S.X₃ h₃ e₃)) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R)
        (Module.finrank (IsLocalRing.ResidueField R) S.X₂)
        (exactSequence S h₁ h₂ h₃ e₁ e₃ ∘
          Fin.cast (length_eq_finrank R S.X₂ h₂ hAnn₂).symm) := sorry

end Module.FiniteLengthDeterminant
