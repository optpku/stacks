module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect.ResidueField
import StacksCheckRecall

/-!
# Lemma 15.84.9

@stack 0DJH
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

noncomputable section

universe u

/- Lemma 15.84.9 (0DJH): the reusable owner keeps the finite-presentation hypothesis together
with the chosen polynomial presentation and states the fiber vanishing on the canonical localized
derived restriction. -/
@[stacks 0DJH "localized relative Tor-amplitude from residue-field homology"]
#check fun {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (d : ℕ) (π : MvPolynomial (Fin d) R →ₐ[R] A) (hπ : Function.Surjective π)
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hlyingOver : Ideal.comap (algebraMap R A) q.asIdeal = p.asIdeal)
    (K : DerivedCategory (ModuleCat A)) (a b : ℤ) (hK : K.IsPseudoCoherent)
    (hκ :
      let Rp := Localization.AtPrime p.asIdeal
      let Aq := Localization.AtPrime q.asIdeal
      let ρ : Rp →+* Aq :=
        Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) hlyingOver.symm
      let Kq := (ModuleCat.derivedExtensionOfScalars (algebraMap A Aq)).obj K
      let KqOverRp := (ModuleCat.derivedRestrictionOfScalars ρ).obj Kq
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero (DerivedCategory.PrimeResidueField.homology (closedPoint Rp) KqOverRp i)) =>
  (DerivedCategory.localized_hasTorAmplitudeIn_over_base_of_pseudoCoherent_of_baseResidueFieldHomology_vanishing
    d π hπ p q hlyingOver K a b hK hκ :
      let Aq := Localization.AtPrime q.asIdeal
      let Kq := (ModuleCat.derivedExtensionOfScalars (algebraMap A Aq)).obj K
      let KqOverR :=
        (ModuleCat.derivedRestrictionOfScalars
          ((algebraMap A Aq).comp (algebraMap R A))).obj Kq
      KqOverR.HasTorAmplitudeIn (R := R) (a - (d : ℤ)) b)

/- The first canonical map used by the owner is derived extension from `A` to `A_q`. -/
#check @ModuleCat.derivedExtensionOfScalars

/- The localized object is then viewed over `R_p` and over `R` by derived restriction. -/
#check @ModuleCat.derivedRestrictionOfScalars

/- The fiber hypothesis uses the canonical prime-residue-field homology object. -/
#check @DerivedCategory.PrimeResidueField.homology

end
