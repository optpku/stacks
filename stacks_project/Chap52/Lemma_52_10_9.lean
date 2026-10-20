/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.Stabilization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn Opposite

noncomputable section

universe u

/- Lemma 52.10.9: under the algebraization hypotheses, sufficiently small
supports have an invertible canonical comparison with the inverse limit of the
adic quotient cohomology system. -/
@[stacks 0EG0] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.exists_stabilizingIdeal_limitComparison :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I a : Ideal A) (hIa : I ≤ a) [IsAdicComplete I A]
      (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (s d : ℤ)
      (hSituation : Ideal.LocalCohomology.AlgebraizationSituation H I M
        (PrimeSpectrum.zeroLocus (a : Set A)) s d)
      (δ : PrimeSpectrum A → ℤ) [IsDimensionFunction δ]
      (δmax δmin : ℤ)
      (hδmax : IsGreatest
        (Set.image δ (PrimeSpectrum.zeroLocus (a : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A))) δmax)
      (hδmin : IsLeast
        (Set.image δ (PrimeSpectrum.zeroLocus (a : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A))) δmin)
      (h_depth : ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          p ∉ PrimeSpectrum.associatedSubset I a →
            ((s + 1 : ℤ) : EInt) ≤
                ((WithTop.map Int.ofNat
                  (moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
              ∀ q : PrimeSpectrum A,
                q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                  PrimeSpectrum.zeroLocus (a : Set A)) ∩
                    PrimeSpectrum.zeroLocus (I : Set A) →
                  ((d + (s + 1 : ℤ)) : EInt) <
                    ((WithTop.map Int.ofNat
                      (moduleDepth (Localization.AtPrime p.asIdeal)
                        (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                      WithBot.map (WithTop.map Int.ofNat)
                        (ringKrullDim (p.asIdeal.quotientAtPrime q)))
      (h_exceptional : ∀ p : PrimeSpectrum A,
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          p ∉ PrimeSpectrum.associatedSubset I a →
          Set.Nonempty
            ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (a : Set A)) ∩
              PrimeSpectrum.zeroLocus (I : Set A)) →
          ((WithTop.map Int.ofNat
            (moduleDepth (Localization.AtPrime p.asIdeal)
              (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) <
            ((s + 1 : ℤ) : EInt) →
          (WithBot.map (WithTop.map Int.ofNat)
              (Module.supportDim (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) < ((s + 3 : ℤ) : EInt)) ∨
            δ p > d + δmax - 1 ∨
              ∀ q : PrimeSpectrum A,
                q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                  PrimeSpectrum.zeroLocus (a : Set A)) ∩
                    PrimeSpectrum.zeroLocus (I : Set A) →
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                      WithBot.map (WithTop.map Int.ofNat)
                        (ringKrullDim (p.asIdeal.quotientAtPrime q)) >
                    ((d + (s + 1 : ℤ) + δmax - δmin - 2 : ℤ) : EInt)),
      ∃ J₀ : Ideal A, ∃ hJ₀ : J₀ ≤ a,
        PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (a : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) ∧
        ∀ (J : Ideal A) (hJ : J ≤ J₀)
          (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A) =
            PrimeSpectrum.zeroLocus (a : Set A) ∩
              PrimeSpectrum.zeroLocus (I : Set A)),
          IsIso (CategoryTheory.ModuleCat.SupportedOn.adicSupportLimitComparison
            I a J (hJ.trans hJ₀) hV (ModuleCat.of A M) (s + 1)))

end
