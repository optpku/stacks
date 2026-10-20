module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ResidueField.PrimeFreeModel
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.TorAmplitude.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative perfectness from residue-field fibers

This leaf owns the local Tor-amplitude estimate and the global fiberwise criterion for relative
perfectness over a flat finitely presented algebra.

@stack 0DJH
@stack 0GHJ
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing

universe u

namespace CategoryTheory.DerivedCategory

/-- Lemma 15.84.9 (0DJH): let `A` be a flat finitely presented `R`-algebra with a
surjective presentation by a polynomial algebra in `d` variables. If `q : Spec(A)` lies over
`p : Spec(R)`, a pseudo-coherent `K : D(A)` whose localized fiber over `κ(p)` has homology
only in `[a, b]` has localized Tor-amplitude `[a - d, b]` over `R`. -/
@[stacks 0DJH "localized relative Tor-amplitude from residue-field homology"]
theorem localized_hasTorAmplitudeIn_over_base_of_pseudoCoherent_of_baseResidueFieldHomology_vanishing
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
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
        IsZero (PrimeResidueField.homology (closedPoint Rp) KqOverRp i)) :
    let Aq := Localization.AtPrime q.asIdeal
    let Kq := (ModuleCat.derivedExtensionOfScalars (algebraMap A Aq)).obj K
    let KqOverR :=
      (ModuleCat.derivedRestrictionOfScalars
        ((algebraMap A Aq).comp (algebraMap R A))).obj Kq
    HasTorAmplitudeIn (R := R) KqOverR (a - (d : ℤ)) b := sorry
/- Proof strategy: pass to the local rings `R_p → A_q`, use the chosen `d`-variable polynomial
presentation and the prime free-model comparison to convert residue-field homology vanishing into
the regular closed-fiber Tor-amplitude estimate, then transport the resulting interval along
localization and the scalar-tower restriction comparison back to `R`. -/

/-- Lemma 15.84.10 (0GHJ): for a flat finitely presented map `R → A` and a
pseudo-coherent `K : D(A)`, relative perfectness over `R` is equivalent to boundedness below of
`K` and of every derived residue-field fiber over `Spec(R)`. -/
@[stacks 0GHJ "relative perfectness detected by bounded residue-field fibers"]
theorem isPerfectOver_iff_boundedBelow_and_primeResidueFields_boundedBelow
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) (hK : K.IsPseudoCoherent) :
    IsPerfectOver R K ↔
      (∃ n : ℤ, K.IsGE n) ∧
        ∀ p : PrimeSpectrum R, ∃ n : ℤ,
          ((ModuleCat.derivedExtensionOfScalars
            (algebraMap R p.asIdeal.ResidueField)).obj
            ((ModuleCat.derivedRestrictionOfScalars (algebraMap R A)).obj K)).IsGE n := sorry
/- Proof strategy: in the forward direction use finite Tor dimension after restriction and scalar
extension to every residue field.  Conversely, localize at each prime, choose a finite polynomial
presentation, apply
`localized_hasTorAmplitudeIn_over_base_of_pseudoCoherent_of_baseResidueFieldHomology_vanishing`,
and combine the resulting local lower bounds with pseudo-coherence and local detection of finite
Tor dimension; finish with `isPerfectOver_iff`. -/

end CategoryTheory.DerivedCategory
