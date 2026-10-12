/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.WithBotTop
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Annihilator
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.CohomologicalDimension
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.DerivedCompletion

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/-- Under a dualizing-complex hypothesis and a localized depth bound, derived completed
local cohomology is annihilated away from a prescribed prime in the stated degrees. -/
theorem exists_commonAnnihilator_derivedCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I J : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (s d : ℤ)
    (h_not_mem : p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩
      PrimeSpectrum.zeroLocus (I : Set A))
    (h_cd : HasDimensionLE I d)
    (h_depth : ∀ p' q : PrimeSpectrum A,
      p'.asIdeal ≤ p.asIdeal →
        q ∈ (PrimeSpectrum.zeroLocus (p'.asIdeal : Set A) ∩
          PrimeSpectrum.zeroLocus (J : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A) →
          ((d + s : ℤ) : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p'.asIdeal)
                (LocalizedModule.AtPrime p'.asIdeal M)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (p'.asIdeal.quotientAtPrime q))) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.derivedCompletionOf I I.fg_of_isNoetherianRing
            ((ModuleCat.SupportedOn.derivedInclusion
              (PrimeSpectrum.zeroLocus (J : Set A))).obj
                ((ModuleCat.SupportedOn.derivedSections
                  (PrimeSpectrum.zeroLocus (J : Set A))).obj
                    (ModuleCat.single0 (ModuleCat.of A M)))))) := sorry

/-- Over a Noetherian local ring with a dualizing complex, a bound `cd(A, I) ≤ d`
and a localized depth plus quotient-dimension bound greater than `d + s` imply
that an element outside the chosen prime annihilates every cohomology module
through degree `s` of the derived `I`-adic completion of maximal-ideal local cohomology. -/
theorem exists_commonAnnihilator_maximalIdeal
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (p : PrimeSpectrum A) (s d : ℤ)
    (h_cd : HasDimensionLE I d)
    (h_depth : ((d + s : ℤ) : EInt) <
      ((WithTop.map Int.ofNat
        (moduleDepth (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat) (ringKrullDim (A ⧸ p.asIdeal))) :
    ∃ f : A, f ∉ p.asIdeal ∧ ∀ i : ℤ, i ≤ s →
      f ∈ Module.annihilator A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          (DerivedCategory.derivedCompletionOf I I.fg_of_isNoetherianRing
            ((ModuleCat.SupportedOn.derivedInclusion
              (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A))).obj
                ((ModuleCat.SupportedOn.derivedSections
                  (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A))).obj
                    (ModuleCat.single0 (ModuleCat.of A M)))))) := sorry

end Ideal.LocalCohomology
