/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Stabilization
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.9.4 -/
@[stacks 0EFQ] #check (Ideal.LocalCohomology.exists_stabilizingIdeal_of_localRing_depth_gt :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))],
    ∀ (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A))),
    (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H) →
    ∀ (I : Ideal A) (hI : I ≠ ⊤) (M : Type u),
      [AddCommGroup M] → [Module A M] → [Module.Finite A M] →
      ∀ (s d : ℤ),
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) =
            {IsLocalRing.closedPoint A} →
            WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal)) ≤ (d : EInt)) →
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) ≠
            {IsLocalRing.closedPoint A} →
            (s : EInt) ≤
                ((WithTop.map Int.ofNat
                  (moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
              ((d + s : ℤ) : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim (A ⧸ p.asIdeal))) →
      (∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) =
            {IsLocalRing.closedPoint A} →
            (s : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)) →
      ∃ J₀ : Ideal A,
        PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} ∧
        ∀ (J : Ideal A) (hJ : J ≤ J₀),
          PrimeSpectrum.zeroLocus (J : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) =
            {IsLocalRing.closedPoint A} →
            ∀ i : ℤ, i ≤ s →
              Function.Bijective
                  (ModuleCat.SupportedOn.supportCohomologyMap
                    (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ)
                    (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
                IsIsomorphic
                  (ModuleCat.SupportedOn.cohomology
                    (PrimeSpectrum.zeroLocus (J : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i)
                  (ModuleCat.SupportedOn.cohomology
                    (PrimeSpectrum.zeroLocus
                      (IsLocalRing.maximalIdeal A : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
                Module.IsAnnihilatedByPower I
                  (ModuleCat.SupportedOn.cohomology
                    (PrimeSpectrum.zeroLocus (J₀ : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
                Module.IsAnnihilatedByPower I
                  (ModuleCat.SupportedOn.cohomology
                    (PrimeSpectrum.zeroLocus (J : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
                Module.IsAnnihilatedByPower I
                  (ModuleCat.SupportedOn.cohomology
                    (PrimeSpectrum.zeroLocus
                      (IsLocalRing.maximalIdeal A : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i))

end Ideal.LocalCohomology
