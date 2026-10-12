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

/- Lemma 52.8.4 -/
@[stacks 0EFK] #check
  (Ideal.LocalCohomology.exists_stabilizingIdeal_of_depth_gt :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (h_dualizing :
        ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
      (I J : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (s d : ℤ)
      (h_dimension : ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          p ∈ PrimeSpectrum.associatedSubset I J →
            ∃ q : PrimeSpectrum A,
              q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (J : Set A)) ∩
                  PrimeSpectrum.zeroLocus (I : Set A) ∧
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q)) ≤ (d : EInt))
      (h_depth : ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          p ∉ PrimeSpectrum.associatedSubset I J →
            (s : EInt) ≤
                ((WithTop.map Int.ofNat
                  (moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
              ∀ q : PrimeSpectrum A,
                q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                  PrimeSpectrum.zeroLocus (J : Set A)) ∩
                    PrimeSpectrum.zeroLocus (I : Set A) →
                  ((d + s : ℤ) : EInt) <
                    ((WithTop.map Int.ofNat
                      (moduleDepth (Localization.AtPrime p.asIdeal)
                        (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                      WithBot.map (WithTop.map Int.ofNat)
                        (ringKrullDim (p.asIdeal.quotientAtPrime q)))
      (h_depth_T : ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          p ∈ PrimeSpectrum.associatedSubset I J →
            (s : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)),
      ∃ J₀ : Ideal A, ∃ hJ₀ : J₀ ≤ J,
        PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) ∧
        (∀ (J' : Ideal A) (hJ' : J' ≤ J₀),
          PrimeSpectrum.zeroLocus (J' : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) =
            PrimeSpectrum.zeroLocus (J : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) →
            ∀ i : ℤ, i ≤ s →
              Function.Bijective
                  (ModuleCat.SupportedOn.supportCohomologyMap
                    (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ')
                    (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
                Module.IsAnnihilatedByPower (J₀ * I)
                  (ModuleCat.SupportedOn.cohomology
                    (PrimeSpectrum.zeroLocus (J' : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i)) ∧
        ∀ i : ℤ, i ≤ s →
          (Function.Bijective
                (ModuleCat.SupportedOn.supportCohomologyMap
                  (PrimeSpectrum.zeroLocus_anti_mono_ideal
                    (le_sup_left : J ≤ J + I))
                  (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
              Function.Bijective
                (ModuleCat.SupportedOn.supportCohomologyMap
                  (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ₀)
                  (ModuleCat.single0 (ModuleCat.of A M)) i)) ∧
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
                    (PrimeSpectrum.zeroLocus (J + I : Set A))
                    (ModuleCat.single0 (ModuleCat.of A M)) i))

end Ideal.LocalCohomology
