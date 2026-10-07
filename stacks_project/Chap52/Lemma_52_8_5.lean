module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion.Stabilization

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.8.5: under the Noetherian, finite-module, dualizing-complex, and
`I`-adic completeness hypotheses, together with the cohomological-dimension,
depth, support-dimension, and dimension-function alternatives, an ideal `J₀ ≤ J`
stabilizes the support-to-derived-completion comparison through degree `s`. -/
@[stacks 0EFL] #check (Ideal.LocalCohomology.exists_stabilizingIdeal_derivedCompletion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I J : Ideal A) [IsAdicComplete I A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s d : ℤ)
    (δ : PrimeSpectrum A → ℤ) [IsDimensionFunction δ]
    (δmax δmin : ℤ)
    (hδmax : IsGreatest
      (δ '' (PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmax)
    (hδmin : IsLeast
      (δ '' (PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmin)
    (h_cd : HasDimensionLE I d)
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
    (h_exceptional : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.associatedSubset I J →
        Set.Nonempty
          ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (J : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A)) →
        ((WithTop.map Int.ofNat
          (moduleDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) <
          (s : EInt) →
          (WithBot.map (WithTop.map Int.ofNat)
              (Module.supportDim (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) < ((s + 2 : ℤ) : EInt)) ∨
            δ p > d + δmax - 1 ∨
              ∀ q : PrimeSpectrum A,
                q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                  PrimeSpectrum.zeroLocus (J : Set A)) ∩
                    PrimeSpectrum.zeroLocus (I : Set A) →
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                      WithBot.map (WithTop.map Int.ofNat)
                        (ringKrullDim (p.asIdeal.quotientAtPrime q)) >
                    ((d + s + δmax - δmin - 2 : ℤ) : EInt)),
    ∃ J₀ : Ideal A, ∃ hJ₀ : J₀ ≤ J,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ (J' : Ideal A) (hJ' : J' ≤ J₀),
        (hV' : PrimeSpectrum.zeroLocus (J' : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (J : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A)) →
          ∀ i : ℤ, i ≤ s →
            IsIso
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
                (derivedCompletionComparison I J J' (hJ'.trans hJ₀)
                  (ModuleCat.single0 (ModuleCat.of A M))
                  (derivedCompletionSupportMapIsIso I J J' (hJ'.trans hJ₀) hV'
                    (ModuleCat.single0 (ModuleCat.of A M))))))

end Ideal.LocalCohomology
