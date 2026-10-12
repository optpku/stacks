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

/- Lemma 52.8.2: let `I` and `J` be ideals of a Noetherian ring `A`, let `M` be a
finite `A`-module, and let `s d : ℤ`. Assume `A` has a dualizing complex. Outside
`V(I)`, impose the stated quotient-dimension condition on primes in
`PrimeSpectrum.associatedSubset I J` and the stated depth alternative on primes
outside that subset. Then there is `J₀ ≤ J` with
`V(J₀) ∩ V(I) = V(J) ∩ V(I)` such that every further `J' ≤ J₀` with the same
intersection has the same supported cohomology through degree `s`, uniformly
annihilated by a power of `J₀ * I`.

The canonical support map runs from support in `V(J₀)` to support in `V(J')`;
its asserted bijectivity recovers the inverse direction displayed in the source. -/
@[stacks 0EFI] #check (Ideal.LocalCohomology.exists_stabilizingIdeal :
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
                      (ringKrullDim (p.asIdeal.quotientAtPrime q))),
    ∃ J₀ : Ideal A, J₀ ≤ J ∧
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (J : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ (J' : Ideal A) (hJ' : J' ≤ J₀),
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
                  (ModuleCat.single0 (ModuleCat.of A M)) i))

end Ideal.LocalCohomology
