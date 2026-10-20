module

public import Mathlib.Order.WithBotTop
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.NonminimalPrimes
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.Spectrum.Prime.AssociatedSubset

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/-- For a finite module over a Noetherian ring admitting a dualizing complex, localized
depth and quotient-dimension bounds outside `V(I)` yield an ideal `J₀ ≤ J` preserving
`V(J) ∩ V(I)` such that supported cohomology stabilizes through degree `s` for all
further ideals with the same intersection and is annihilated by a power of `J₀ * I`. -/
theorem exists_stabilizingIdeal
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
                      (ringKrullDim (p.asIdeal.quotientAtPrime q))) :
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
                  (ModuleCat.single0 (ModuleCat.of A M)) i) := sorry

/-- In a Noetherian local ring with a dualizing complex, dimension and depth
conditions outside `V(I)` produce an ideal whose zero locus meets `V(I)` only
at the closed point and whose smaller ideals preserve supported cohomology in
the indicated degrees. -/
theorem exists_stabilizingIdeal_of_localRing
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
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
                  (ringKrullDim (A ⧸ p.asIdeal))) :
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
                  (ModuleCat.single0 (ModuleCat.of A M)) i) := sorry

/-- If the localized depth on the associated-prime locus outside `V(I)` is
strictly larger than `s`, the stabilizing ideal also compares the supported
cohomology for `J + I`, `J`, and `J₀` through degree `s`, with each module
annihilated by a power of `I`. -/
theorem exists_stabilizingIdeal_of_depth_gt
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
    (h_depth_T : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∈ PrimeSpectrum.associatedSubset I J →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)) :
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
                  (ModuleCat.single0 (ModuleCat.of A M)) i) := sorry

/-- A local-ring specialization of the stabilization theorem with strict depth
on the locus whose intersection with `V(I)` is the closed point. -/
theorem exists_stabilizingIdeal_of_localRing_depth_gt
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
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
    (h_depth_T : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)) :
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
                  (ModuleCat.single0 (ModuleCat.of A M)) i) := sorry

end Ideal.LocalCohomology
