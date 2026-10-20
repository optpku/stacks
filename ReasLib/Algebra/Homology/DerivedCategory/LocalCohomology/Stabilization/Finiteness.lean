/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Stabilization

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/-- For a finite module over a Noetherian ring admitting a dualizing complex,
localized depth and quotient-dimension bounds produce an ideal `J₀ ≤ J` preserving
`V(J) ∩ V(I)` whose supported cohomology stabilizes under further refinements
through degree `s` and is annihilated by a power of `J₀ * I`. An additional strict
depth-plus-dimension bound on `V(I)` outside `V(J) ∩ V(I)` ensures that the
supported cohomology of this same ideal is finite through degree `s`. -/
theorem exists_stabilizingIdeal_with_finiteCohomology
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
                    (ringKrullDim (p.asIdeal.quotientAtPrime q))) :
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
            (ModuleCat.single0 (ModuleCat.of A M)) i) := sorry

/-- For a finite module over a Noetherian local ring admitting a dualizing
complex, dimension and depth bounds outside `V(I)`, together with a strict
depth-plus-dimension bound on `V(I)` away from the closed point, yield an ideal
`J₀` whose zero locus meets `V(I)` only at the closed point. For every smaller
ideal with the same intersection, supported cohomology stabilizes through
degree `s` and is annihilated by a power of `J₀ * I`; the supported cohomology
of this same `J₀` is finite through degree `s`. -/
theorem exists_stabilizingIdeal_of_localRing_cohomology_finite
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
    (h_depth_on_VI : ∀ p : PrimeSpectrum A,
      p ∈ PrimeSpectrum.zeroLocus (I : Set A) →
        p ≠ IsLocalRing.closedPoint A →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (A ⧸ p.asIdeal))) :
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
            (ModuleCat.single0 (ModuleCat.of A M)) i) := sorry

end Ideal.LocalCohomology
