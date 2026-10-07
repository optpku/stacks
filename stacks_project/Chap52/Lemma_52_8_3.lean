module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Stabilization.Finiteness
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 52.8.3: under the hypotheses of `exists_stabilizingIdeal`, assume that
for every `p ∈ V(I)` outside `V(J) ∩ V(I)`, and every
`q ∈ V(p) ∩ V(J) ∩ V(I)`, the localized depth plus quotient dimension is
strictly greater than `s`. The same ideal `J₀ ≤ J` retains the intersection,
refinement-stabilization, and power-annihilation properties and has finite
supported cohomology through degree `s`. -/
@[stacks 0EFJ] #check
  (Ideal.LocalCohomology.exists_stabilizingIdeal_with_finiteCohomology :
    ∀
    {A : Type u} [CommRing A] [IsNoetherianRing A]
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
    (h_depth_on_VI : ∀ p : PrimeSpectrum A,
      p ∈ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.zeroLocus (J : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) →
          ∀ q : PrimeSpectrum A,
            q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (J : Set A)) ∩
                PrimeSpectrum.zeroLocus (I : Set A) →
              (s : EInt) <
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
        Module.Finite A
          (ModuleCat.SupportedOn.cohomology
            (PrimeSpectrum.zeroLocus (J₀ : Set A))
            (ModuleCat.single0 (ModuleCat.of A M)) i))
