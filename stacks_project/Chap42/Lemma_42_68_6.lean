/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functoriality
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.Naturality
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ThreeByThree
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact.ExteriorPower

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/- Lemma 42.68.6 (1): a short exact sequence of finite-length modules over a local ring has
a canonical determinant-line equivalence, given on nonzero symbols by concatenation. -/
@[stacks 02PA] #check (Module.FiniteLengthDeterminant.exactEquiv :
  ∀ (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact),
    Module.FiniteLengthDeterminant R S.X₁ h₁ ⊗[IsLocalRing.ResidueField R]
        Module.FiniteLengthDeterminant R S.X₃ h₃ ≃ₗ[IsLocalRing.ResidueField R]
      Module.FiniteLengthDeterminant R S.X₂ h₂)

#check (Module.FiniteLengthDeterminant.exactEquiv_tmul_symbol :
  ∀ (S : ShortComplex (ModuleCat.{v} R))
    (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
    (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
    (e₁ : Symbol R S.X₁ h₁) (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0)
    (e₃ : Symbol R S.X₃ h₃),
    exactEquiv S h₁ h₂ h₃ hS
        (symbol R S.X₁ h₁ e₁ ⊗ₜ[IsLocalRing.ResidueField R]
          symbol R S.X₃ h₃ e₃) =
      symbol R S.X₂ h₂
        ⟨exactSequence S h₁ h₂ h₃ e₁ e₃,
          exactSequence_isAdmissible S h₁ h₂ h₃ hS e₁ he₁ e₃⟩)

/- Lemma 42.68.6 (2): the canonical determinant-line equivalence is natural under
isomorphisms of short exact sequences. -/
@[stacks 02PA] #check (Module.FiniteLengthDeterminant.exactEquiv_naturality :
  ∀ {S T : ShortComplex (ModuleCat.{v} R)}
    (hS₁ : IsFiniteLength R S.X₁) (hS₂ : IsFiniteLength R S.X₂)
    (hS₃ : IsFiniteLength R S.X₃) (hT₁ : IsFiniteLength R T.X₁)
    (hT₂ : IsFiniteLength R T.X₂) (hT₃ : IsFiniteLength R T.X₃)
    (hS : S.ShortExact) (e : S ≅ T),
    (exactEquiv T hT₁ hT₂ hT₃ (ShortComplex.shortExact_of_iso e hS)).toLinearMap.comp
        (TensorProduct.congr
          (mapEquiv hS₁ hT₁ (ShortComplex.π₁.mapIso e).toLinearEquiv)
          (mapEquiv hS₃ hT₃ (ShortComplex.π₃.mapIso e).toLinearEquiv)).toLinearMap =
      (mapEquiv hS₂ hT₂ (ShortComplex.π₂.mapIso e).toLinearEquiv).toLinearMap.comp
        (exactEquiv S hS₁ hS₂ hS₃ hS).toLinearMap)

/- Lemma 42.68.6 (3): the row-first and signed column-first determinant maps of an exact
three-by-three diagram agree. -/
@[stacks 02PA] #check (Module.FiniteLengthDeterminant.ThreeByThree.commutes :
  ∀ D : ThreeByThree.{u, v} R, ThreeByThree.viaRows D = ThreeByThree.viaColumns D)

/- Lemma 42.68.6 (4): for residue-field vector spaces, the canonical determinant-line map
agrees with concatenation in the top exterior power. -/
@[stacks 02PA] #check
  (Module.FiniteLengthDeterminant.exactEquiv_toExteriorPower_tmul_symbol :
    ∀ (S : ShortComplex (ModuleCat.{v} R))
      (h₁ : IsFiniteLength R S.X₁) (h₂ : IsFiniteLength R S.X₂)
      (h₃ : IsFiniteLength R S.X₃) (hS : S.ShortExact)
      (hAnn₁ : Module.IsTorsionBySet R S.X₁ (IsLocalRing.maximalIdeal R))
      (hAnn₂ : Module.IsTorsionBySet R S.X₂ (IsLocalRing.maximalIdeal R))
      (hAnn₃ : Module.IsTorsionBySet R S.X₃ (IsLocalRing.maximalIdeal R))
      (e₁ : Symbol R S.X₁ h₁) (he₁ : symbol R S.X₁ h₁ e₁ ≠ 0)
      (e₃ : Symbol R S.X₃ h₃) (he₃ : symbol R S.X₃ h₃ e₃ ≠ 0),
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
