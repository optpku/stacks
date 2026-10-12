/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Stabilization.Finiteness

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.9.3: under the hypotheses of Lemma 52.9.2, if every prime
`p ∈ V(I)` other than the closed point satisfies
`moduleDepth (Localization.AtPrime p.asIdeal)
  (LocalizedModule.AtPrime p.asIdeal M) + ringKrullDim (A ⧸ p.asIdeal) > s`,
then there is one ideal `J₀` with `V(J₀) ∩ V(I)` equal to the closed point
such that for every `J' ≤ J₀` with the same intersection, the supported
cohomology comparison is bijective through degree `s` and these modules are
annihilated by a power of `J₀ * I`. The supported cohomology of this same `J₀`
is finite over `A` through degree `s`. -/
@[stacks 0DXN] #check (Ideal.LocalCohomology.exists_stabilizingIdeal_of_localRing_cohomology_finite :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (I : Ideal A) (hI : I ≠ ⊤) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s d : ℤ)
    (h_dimension : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
          WithBot.map (WithTop.map Int.ofNat)
              (ringKrullDim (A ⧸ p.asIdeal)) ≤ (d : EInt))
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
                  (ringKrullDim (A ⧸ p.asIdeal)))
    (h_depth_on_VI : ∀ p : PrimeSpectrum A,
      p ∈ PrimeSpectrum.zeroLocus (I : Set A) →
        p ≠ IsLocalRing.closedPoint A →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal))),
    ∃ J₀ : Ideal A,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) =
        {IsLocalRing.closedPoint A} ∧
      (∀ (J' : Ideal A) (hJ' : J' ≤ J₀),
        PrimeSpectrum.zeroLocus (J' : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
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
        Module.Finite A
          (ModuleCat.SupportedOn.cohomology
            (PrimeSpectrum.zeroLocus (J₀ : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) i))

end Ideal.LocalCohomology
