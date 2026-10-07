module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.LocalizationAway
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.PrimeFreeModel
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

/-!
# Recognizing perfect complexes from residue-field fibers

@stack 0BYP
@stack 068V
@stack 068W

This leaf owns the prime-local free-model and residue-field criteria for recognizing perfect
pseudo-coherent derived objects.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra

universe u

-- Local instance justification (search instability): derived scalar extension is formed in the
-- standard t-structure on derived categories of modules.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/-- Lemma 15.78.1 (1) (0BYP): if a pseudo-coherent bounded-below object has zero-dimensional
prime-residue-field homology below `a`, then after one principal localization it has a
bounded-above finite-free representative whose terms have the prescribed fiber dimensions. -/
@[stacks 0BYP "localized finite-free model with prescribed residue-field ranks"]
theorem exists_away_termwiseFree_representative_of_primeResidueFieldDerivedHomology_of_isPseudoCoherent_of_isGE
    (p : PrimeSpectrum R) (K : DMod) (a : ℤ) (hK : K.IsPseudoCoherent)
    (hboundedBelow : ∃ n : ℤ, K.IsGE n)
    (hda : ∀ i : ℤ, i < a →
      Module.rank p.asIdeal.ResidueField
        (DerivedCategory.PrimeResidueField.homology p K i) = 0) :
    ∃ f : R, f ∉ p.asIdeal ∧
      ∃ P : DerivedCategory.PrimeResidueField.AwayBoundedFiniteFree f,
        (P : CochainComplex (ModuleCat (Localization.Away f)) ℤ).IsStrictlyGE a ∧
          (∀ i : ℤ,
            Nonempty
              (((P : CochainComplex (ModuleCat (Localization.Away f)) ℤ).X i) ≃ₗ[
                Localization.Away f]
                (Fin (Module.finrank p.asIdeal.ResidueField
                  (DerivedCategory.PrimeResidueField.homology p K i)) →
                    Localization.Away f))) ∧
          Nonempty
            ((K ⊗[R]^L[Localization.Away f]) ≅
              DerivedCategory.Q.obj
                (P : CochainComplex (ModuleCat (Localization.Away f)) ℤ)) := sorry

/-- Lemma 15.78.1 (2) (0BYP): under the same residue-field vanishing hypothesis, one principal
localization makes the pseudo-coherent bounded-below object perfect. -/
@[stacks 0BYP "localized perfectness from residue-field vanishing below"]
theorem exists_away_isPerfect_of_primeResidueFieldDerivedHomology_vanishing_below
    (p : PrimeSpectrum R) (K : DMod) (a : ℤ) (hK : K.IsPseudoCoherent)
    (hboundedBelow : ∃ n : ℤ, K.IsGE n)
    (hda : ∀ i : ℤ, i < a →
      Module.rank p.asIdeal.ResidueField
        (DerivedCategory.PrimeResidueField.homology p K i) = 0) :
    ∃ f : R, f ∉ p.asIdeal ∧
      (K ⊗[R]^L[Localization.Away f]).IsPerfect := sorry

/-- Lemma 15.78.2 (068V): for a pseudo-coherent object, perfectness with Tor-amplitude in
`[a, b]` is equivalent to homology vanishing outside `[a, b]` on every prime residue field and
on every maximal residue field. -/
@[stacks 068V "Tor amplitude detected on prime and maximal residue fields"]
theorem perfect_torAmplitude_tfae_prime_and_maximal_residueField_homology_vanishing_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE
      [ K.IsPerfect ∧ DerivedCategory.HasTorAmplitudeIn (R := R) K a b
      , ∀ p : PrimeSpectrum R, ∀ i : ℤ, i ∉ Set.Icc a b →
          IsZero (DerivedCategory.PrimeResidueField.homology p K i)
      , ∀ (m : PrimeSpectrum R) (_ : m.asIdeal.IsMaximal) (i : ℤ), i ∉ Set.Icc a b →
          IsZero (DerivedCategory.PrimeResidueField.homology m K i)
      ] := sorry

/-- Lemma 15.78.3 (1) (068W): for a pseudo-coherent object, perfectness after localization at
all primes, perfectness after localization at all maximal ideals, and eventual lower homology
vanishing on the corresponding residue fields are equivalent. -/
@[stacks 068W "local perfectness and eventual residue-field vanishing"]
theorem prime_and_maximal_localizations_and_residueField_vanishing_tfae_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    List.TFAE
      [ ∀ p : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime p.asIdeal]).IsPerfect
      , ∀ m : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime m.asIdeal]).IsPerfect
      , ∀ p : PrimeSpectrum R, ∃ a : ℤ, ∀ i : ℤ, i < a →
          IsZero (DerivedCategory.PrimeResidueField.homology p K i)
      , ∀ m : MaximalSpectrum R, ∃ a : ℤ, ∀ i : ℤ, i < a →
          IsZero (DerivedCategory.PrimeResidueField.homology m.toPrimeSpectrum K i)
      ] := sorry

/-- Lemma 15.78.3 (2) (068W): if the pseudo-coherent object is bounded below, global
perfectness joins the equivalent prime-local, maximal-local, and residue-field conditions. -/
@[stacks 068W "global perfectness recognized by local and residue-field conditions"]
theorem perfect_primeLocalizations_maximalLocalizations_residueField_vanishing_tfae_of_isPseudoCoherent_of_isGE
    (K : DMod) (hK : K.IsPseudoCoherent) (hboundedBelow : ∃ n : ℤ, K.IsGE n) :
    List.TFAE
      [ K.IsPerfect
      , ∀ p : PrimeSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime p.asIdeal]).IsPerfect
      , ∀ m : MaximalSpectrum R,
          (K ⊗[R]^L[Localization.AtPrime m.asIdeal]).IsPerfect
      , ∀ p : PrimeSpectrum R, ∃ a : ℤ, ∀ i : ℤ, i < a →
          IsZero (DerivedCategory.PrimeResidueField.homology p K i)
      , ∀ m : MaximalSpectrum R, ∃ a : ℤ, ∀ i : ℤ, i < a →
          IsZero (DerivedCategory.PrimeResidueField.homology m.toPrimeSpectrum K i)
      ] := sorry

end CategoryTheory
