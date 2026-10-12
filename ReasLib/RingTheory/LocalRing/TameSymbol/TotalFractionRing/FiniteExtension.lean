/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.TameSymbol.TotalFractionRing
public import ReasLib.RingTheory.LocalRing.Finite
public import Mathlib.Algebra.BigOperators.Finprod
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

@[expose] public section

/-!
# Tame symbols in finite extensions

This leaf relates the integral tame symbol over a one-dimensional local ring to the symbols
over the maximal localizations of a finite algebra.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators nonZeroDivisors

universe u v

namespace TameSymbol.Total

/-- A maximal localization of a module-finite algebra over a Noetherian ring is Noetherian,
with the base ring kept explicit because it is not determined by the localization. -/
theorem localizationAtPrime_isNoetherianRing
    (A : Type u) {B : Type v} [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (j : MaximalSpectrum B) :
    IsNoetherianRing (Localization.AtPrime j.asIdeal) := sorry

/-- Every maximal localization of a finite extension satisfying the closed-point support and
associated-prime hypotheses is one-dimensional. -/
theorem localizationAtPrime_ringKrullDim_eq_one
    {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (hdim : ringKrullDim A = 1)
    (hinjective : Function.Injective (algebraMap A B))
    (hcoker : Module.IsAnnihilatedByPower (maximalIdeal A)
      (B ⧸ (Algebra.linearMap A B).range))
    (hassociated : maximalIdeal A ∉ associatedPrimesOfModule A B)
    (j : MaximalSpectrum B) :
    ringKrullDim (Localization.AtPrime j.asIdeal) = 1 := sorry

/-- A base nonzerodivisor remains a nonzerodivisor in every maximal localization of a finite
extension satisfying the closed-point support and associated-prime hypotheses. -/
theorem map_mem_nonZeroDivisors_localizationAtPrime
    {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (hdim : ringKrullDim A = 1)
    (hinjective : Function.Injective (algebraMap A B))
    (hcoker : Module.IsAnnihilatedByPower (maximalIdeal A)
      (B ⧸ (Algebra.linearMap A B).range))
    (hassociated : maximalIdeal A ∉ associatedPrimesOfModule A B)
    {a : A} (ha : a ∈ nonZeroDivisors A) (j : MaximalSpectrum B) :
    algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a) ∈
      nonZeroDivisors (Localization.AtPrime j.asIdeal) := sorry

/-- For a finite injective extension of a one-dimensional Noetherian local ring whose quotient
is annihilated by a maximal-ideal power and whose maximal ideal is not associated to the
extension, the tame symbol of two nonzerodivisors is the product of the residue-field norms of
their symbols in all maximal localizations. -/
theorem integralValue_eq_finprod_residueNorm_localizations
    {A : Type u} {B : Type v}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B]
    (hdim : ringKrullDim A = 1)
    (hinjective : Function.Injective (algebraMap A B))
    (hcoker : Module.IsAnnihilatedByPower (maximalIdeal A)
      (B ⧸ (Algebra.linearMap A B).range))
    (hassociated : maximalIdeal A ∉ associatedPrimesOfModule A B)
    (a b : A⁰) :
    Units.map (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).toMonoidHom
        (integralValue A hdim a b) =
      ∏ᶠ j : MaximalSpectrum B,
        TameSymbol.residueNorm A j
          (MaximalSpectrum.liesOver_maximalIdeal_of_moduleFinite A j)
          ((@integralValue (Localization.AtPrime j.asIdeal) _ _
              (localizationAtPrime_isNoetherianRing A j))
            (localizationAtPrime_ringKrullDim_eq_one
              hdim hinjective hcoker hassociated j)
            ⟨algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a),
              map_mem_nonZeroDivisors_localizationAtPrime
                hdim hinjective hcoker hassociated a.property j⟩
            ⟨algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B b),
              map_mem_nonZeroDivisors_localizationAtPrime
                hdim hinjective hcoker hassociated b.property j⟩) := sorry

end TameSymbol.Total

end
