/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Stabilization

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/- Lemma 52.9.2: for a Noetherian local ring `A` with a dualizing complex, an
ideal `I`, and a finite module `M`, assume that primes outside `V(I)` whose
intersection with `V(I)` is the closed point have quotient dimension at most
`d`, while all other such primes satisfy the stated depth/dimension
alternative. Then there is an ideal `J₀` with
`V(J₀) ∩ V(I) = {IsLocalRing.closedPoint A}` such that every `J ≤ J₀` with
the same intersection induces a bijection on supported cohomology through
degree `s`, and the resulting modules are annihilated by a power of `J₀ * I`. -/
@[stacks 0DXM] #check (Ideal.LocalCohomology.exists_stabilizingIdeal_of_localRing :
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
            Function.Bijective
                (ModuleCat.SupportedOn.supportCohomologyMap
                  (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ)
                  (ModuleCat.single0 (ModuleCat.of A M)) i) ∧
              Module.IsAnnihilatedByPower (J₀ * I)
                (ModuleCat.SupportedOn.cohomology
                  (PrimeSpectrum.zeroLocus (J : Set A))
                  (ModuleCat.single0 (ModuleCat.of A M)) i))

end Ideal.LocalCohomology
