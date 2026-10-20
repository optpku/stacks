/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion.Stabilization

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.9.5: for a Noetherian local ring `A` with a proper ideal `I`, an `I`-adically complete
ring and a dualizing complex, a finite `A`-module `M`, the bound
`HasDimensionLE I d`, and the stated depth/dimension alternative away from
`V(I)` and the closed point, there is an ideal `J₀` with
`V(J₀) ∩ V(I) = {IsLocalRing.closedPoint A}` such that every admissible
`J ≤ J₀` has its derived `I`-adic completion map inducing an isomorphism on
homology in every degree `i ≤ s`. -/
@[stacks 0DXP] #check
  (Ideal.LocalCohomology.exists_stabilizingIdeal_of_localRing_derivedCompletion :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I : Ideal A) (hI : I ≠ ⊤) [IsAdicComplete I A] (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s d : ℤ) (h_cd : HasDimensionLE I d)
    (h_depth : ∀ p : PrimeSpectrum A,
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
                  (ringKrullDim (A ⧸ p.asIdeal))),
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) =
        {IsLocalRing.closedPoint A} ∧
      ∀ (J : Ideal A) (hJ : J ≤ J₀),
        PrimeSpectrum.zeroLocus (J : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
          ∀ i : ℤ, i ≤ s →
            IsIso
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
                (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
                  ((ModuleCat.SupportedOn.derivedInclusion
                    (PrimeSpectrum.zeroLocus (J : Set A))).obj
                    ((ModuleCat.SupportedOn.derivedSections
                      (PrimeSpectrum.zeroLocus (J : Set A))).obj
                      (ModuleCat.single0 (ModuleCat.of A M)))))))

end Ideal.LocalCohomology
