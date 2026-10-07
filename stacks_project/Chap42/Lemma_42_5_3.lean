module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing.FiniteExtension
import StacksCheckRecall

@[expose] public section

noncomputable section

open IsLocalRing
open scoped BigOperators nonZeroDivisors

universe u v

/- Lemma 42.5.3: for a finite injective extension of a one-dimensional Noetherian local
ring whose quotient is annihilated by a maximal-ideal power and whose maximal ideal is not
associated to the extension, the tame symbol of two nonzerodivisors is the product of the
residue-field norms of the symbols in all maximal localizations. -/
@[stacks 0EAT] #check (TameSymbol.Total.integralValue_eq_finprod_residueNorm_localizations :
  {A : Type u} → {B : Type v} →
    [CommRing A] → [IsLocalRing A] → [IsNoetherianRing A] →
    [CommRing B] → [Algebra A B] → [Module.Finite A B] →
    (hdim : ringKrullDim A = 1) →
    (hinjective : Function.Injective (algebraMap A B)) →
    (hcoker : Module.IsAnnihilatedByPower (maximalIdeal A)
      (B ⧸ (Algebra.linearMap A B).range)) →
    (hassociated : maximalIdeal A ∉ associatedPrimesOfModule A B) →
    (a b : A⁰) →
    Units.map (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).toMonoidHom
        (TameSymbol.Total.integralValue A hdim a b) =
      ∏ᶠ j : MaximalSpectrum B,
        TameSymbol.residueNorm A j
          (MaximalSpectrum.liesOver_maximalIdeal_of_moduleFinite A j)
          ((@TameSymbol.Total.integralValue (Localization.AtPrime j.asIdeal) _ _
              (TameSymbol.Total.localizationAtPrime_isNoetherianRing A j))
            (TameSymbol.Total.localizationAtPrime_ringKrullDim_eq_one
              hdim hinjective hcoker hassociated j)
            ⟨algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a),
              TameSymbol.Total.map_mem_nonZeroDivisors_localizationAtPrime
                hdim hinjective hcoker hassociated a.property j⟩
            ⟨algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B b),
              TameSymbol.Total.map_mem_nonZeroDivisors_localizationAtPrime
                hdim hinjective hcoker hassociated b.property j⟩))
