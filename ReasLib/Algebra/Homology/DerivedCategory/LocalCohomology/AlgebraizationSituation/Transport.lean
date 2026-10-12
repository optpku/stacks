/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.AdicCompletion.FiniteModule
public import ReasLib.RingTheory.AdicCompletion.Noetherian

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace Ideal.LocalCohomology.AlgebraizationSituation

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- Restricting the locus of an algebraization situation to a specialization-stable subset preserves the situation. -/
theorem restrict
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (T' : Set (PrimeSpectrum A))
    (hT' : StableUnderSpecialization T') (hsub : T' ⊆ T) :
    AlgebraizationSituation H I M T' s d := sorry

/-- Localization transports an algebraization situation along a multiplicative subset. -/
theorem localize
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (S : Submonoid A)
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Localization S)))]
    (Hs : MonoidalClosed (DerivedCategory (ModuleCat.{u} (Localization S)))) :
    AlgebraizationSituation Hs
      (I.map (algebraMap A (Localization S)))
      (LocalizedModule S M)
      {q : PrimeSpectrum (Localization S) |
        PrimeSpectrum.comap (algebraMap A (Localization S)) q ∈ T} s d := sorry

/-- Adic completion transports an algebraization situation to the completed ring and module. -/
theorem complete
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    [MonoidalCategory
      (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))]
    (Hhat : MonoidalClosed
      (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))) :
    AlgebraizationSituation Hhat
      (I.map (algebraMap A (AdicCompletion I A)))
      (AdicCompletion I M)
      {q : PrimeSpectrum (AdicCompletion I A) |
        PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q ∈ T} s d := sorry

end Ideal.LocalCohomology.AlgebraizationSituation
