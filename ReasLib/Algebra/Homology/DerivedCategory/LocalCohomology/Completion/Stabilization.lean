module

public import Mathlib.Order.WithBotTop
public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.RingTheory.Spectrum.Prime.AssociatedSubset
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.ClosedSupport
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.DerivedCompletion.Annihilator

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace Ideal.LocalCohomology

/-- The derived `I`-adic completion of the support map from `V(J)` to `V(J')`
is invertible when the two supports have the same intersection with `V(I)`. -/
theorem derivedCompletionSupportMapIsIso
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J J' : Ideal A) (hJ' : J' ≤ J)
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso
      ((DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).map
        (ModuleCat.SupportedOn.derivedSupportMap
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ') K)) := sorry

/-- The canonical map from sections supported on `V(J')` to the derived `I`-adic
completion of sections supported on `V(J)`, obtained from the completion unit and
the inverse of the completed support map. -/
noncomputable def derivedCompletionComparison
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J J' : Ideal A) (hJ' : J' ≤ J)
    (K : DerivedCategory (ModuleCat.{u} A))
    (h_iso : IsIso
      ((DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).map
        (ModuleCat.SupportedOn.derivedSupportMap
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ') K))) :
    (ModuleCat.SupportedOn.derivedInclusion
        (PrimeSpectrum.zeroLocus (J' : Set A))).obj
        ((ModuleCat.SupportedOn.derivedSections
          (PrimeSpectrum.zeroLocus (J' : Set A))).obj K) ⟶
      DerivedCategory.derivedCompletionOf I I.fg_of_isNoetherianRing
        ((ModuleCat.SupportedOn.derivedInclusion
          (PrimeSpectrum.zeroLocus (J : Set A))).obj
          ((ModuleCat.SupportedOn.derivedSections
            (PrimeSpectrum.zeroLocus (J : Set A))).obj K)) :=
  DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing _ ≫
    @CategoryTheory.inv _ _ _ _
      ((DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).map
        (ModuleCat.SupportedOn.derivedSupportMap
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ') K))
      h_iso

/-- Composing the canonical support-completion comparison with the completed
support map recovers the completion unit on the `V(J')`-supported object. -/
theorem derivedCompletionComparison_comp
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J J' : Ideal A) (hJ' : J' ≤ J)
    (K : DerivedCategory (ModuleCat.{u} A))
    (h_iso : IsIso
      ((DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).map
        (ModuleCat.SupportedOn.derivedSupportMap
          (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ') K))) :
    derivedCompletionComparison I J J' hJ' K h_iso ≫
        (DerivedCategory.derivedCompletion I I.fg_of_isNoetherianRing).map
          (ModuleCat.SupportedOn.derivedSupportMap
            (PrimeSpectrum.zeroLocus_anti_mono_ideal hJ') K) =
      DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
        ((ModuleCat.SupportedOn.derivedInclusion
          (PrimeSpectrum.zeroLocus (J' : Set A))).obj
          ((ModuleCat.SupportedOn.derivedSections
            (PrimeSpectrum.zeroLocus (J' : Set A))).obj K)) := sorry

/-- Under the Noetherian, finite-module, dualizing-complex, and
`I`-adic completeness hypotheses, together with the stated cohomological-dimension,
depth, support-dimension, and dimension-function alternatives, there is an ideal
`J₀ ≤ J` with the same intersection with `V(I)` as `J`. Every `J' ≤ J₀` with the
same intersection has its canonical map to the derived `I`-adic completion of the
`V(J)`-supported derived sections inducing an isomorphism on cohomology through
degree `s`. -/
theorem exists_stabilizingIdeal_derivedCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A]
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
                    ((d + s + δmax - δmin - 2 : ℤ) : EInt)) :
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
                    (ModuleCat.single0 (ModuleCat.of A M))))) := sorry

/-- For a proper ideal `I` in an `I`-adically complete Noetherian local ring with
a dualizing complex, a finite module satisfying the cohomological-dimension bound
and the depth/dimension alternative admits an ideal `J₀` whose zero locus meets
`V(I)` only at the closed point. For every admissible `J ≤ J₀`, the canonical
derived `I`-adic completion map on `V(J)`-supported derived sections induces an
isomorphism on homology in every degree `i ≤ s`. -/
theorem exists_stabilizingIdeal_of_localRing_derivedCompletion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
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
            IsIso
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
                (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing
                  ((ModuleCat.SupportedOn.derivedInclusion
                    (PrimeSpectrum.zeroLocus (J : Set A))).obj
                    ((ModuleCat.SupportedOn.derivedSections
                      (PrimeSpectrum.zeroLocus (J : Set A))).obj
                      (ModuleCat.single0 (ModuleCat.of A M)))))) := sorry

end Ideal.LocalCohomology
