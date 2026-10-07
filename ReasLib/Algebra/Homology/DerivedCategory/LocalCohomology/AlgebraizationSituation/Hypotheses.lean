module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Stabilization
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion.Stabilization
public import ReasLib.RingTheory.Jacobson.Ideal

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace Ideal.LocalCohomology.AlgebraizationSituation

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]

/-- A Jacobson-radical ideal supplies the dimension and depth alternatives for stabilization. -/
theorem stabilizationHypotheses
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (a : Ideal A) (hIa : I ≤ a)
    (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
    (hJac : I ≤ Ring.jacobson A) :
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∈ PrimeSpectrum.associatedSubset I a →
          ∃ q : PrimeSpectrum A,
            q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (a : Set A)) ∩
                PrimeSpectrum.zeroLocus (I : Set A) ∧
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (p.asIdeal.quotientAtPrime q)) ≤ (d : EInt)) ∧
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.associatedSubset I a →
          (s : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ∀ q : PrimeSpectrum A,
              q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (a : Set A)) ∩
                  PrimeSpectrum.zeroLocus (I : Set A) →
                ((d + s : ℤ) : EInt) <
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (p.asIdeal.quotientAtPrime q))) := sorry

/-- Under the Jacobson-radical hypothesis, the strict depth alternative for stabilization also holds. -/
theorem stabilizationDepthHypotheses
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (a : Ideal A) (hIa : I ≤ a)
    (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
    (hJac : I ≤ Ring.jacobson A) :
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∈ PrimeSpectrum.associatedSubset I a →
          ∃ q : PrimeSpectrum A,
            q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (a : Set A)) ∩
                PrimeSpectrum.zeroLocus (I : Set A) ∧
              WithBot.map (WithTop.map Int.ofNat)
                (ringKrullDim (p.asIdeal.quotientAtPrime q)) ≤ (d : EInt)) ∧
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.associatedSubset I a →
          (s : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ∀ q : PrimeSpectrum A,
              q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (a : Set A)) ∩
                  PrimeSpectrum.zeroLocus (I : Set A) →
                ((d + s : ℤ) : EInt) <
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (p.asIdeal.quotientAtPrime q))) ∧
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∈ PrimeSpectrum.associatedSubset I a →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)) := sorry

/-- Adic completeness supplies the dimension and depth alternatives needed for derived completion stabilization. -/
theorem derivedCompletionHypotheses
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (a : Ideal A) (hIa : I ≤ a)
    (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
    [IsAdicComplete I A] :
    HasDimensionLE I d ∧
    ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.associatedSubset I a →
          (s : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ∀ q : PrimeSpectrum A,
              q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (a : Set A)) ∩
                  PrimeSpectrum.zeroLocus (I : Set A) →
                ((d + s : ℤ) : EInt) <
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (p.asIdeal.quotientAtPrime q)) := sorry

/-- In a local ring with maximal ideal `a`, the stabilization dimension and depth hypotheses hold. -/
theorem localStabilizationHypotheses
    [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (a : Ideal A) (hIa : I ≤ a)
    (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
    (hmax : IsLocalRing.maximalIdeal A = a) :
    I ≠ ⊤ ∧
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
          WithBot.map (WithTop.map Int.ofNat)
              (ringKrullDim (A ⧸ p.asIdeal)) ≤ (d : EInt)) ∧
    (∀ p : PrimeSpectrum A,
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
                  (ringKrullDim (A ⧸ p.asIdeal))) := sorry

/-- In a local ring with maximal ideal `a`, the strict depth hypotheses for local stabilization hold. -/
theorem localDepthHypotheses
    [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (a : Ideal A) (hIa : I ≤ a)
    (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
    (hmax : IsLocalRing.maximalIdeal A = a) :
    I ≠ ⊤ ∧
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
          WithBot.map (WithTop.map Int.ofNat)
              (ringKrullDim (A ⧸ p.asIdeal)) ≤ (d : EInt)) ∧
    (∀ p : PrimeSpectrum A,
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
                  (ringKrullDim (A ⧸ p.asIdeal))) ∧
    (∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          {IsLocalRing.closedPoint A} →
          (s : EInt) <
            ((WithTop.map Int.ofNat
              (moduleDepth (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)) := sorry

/-- In a local adically complete ring, the hypotheses for derived-completion stabilization hold. -/
theorem localDerivedCompletionHypotheses
    [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
    (h : AlgebraizationSituation H I M T s d)
    (a : Ideal A) (hIa : I ≤ a)
    (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
    (hmax : IsLocalRing.maximalIdeal A = a)
    [IsAdicComplete I A] :
    HasDimensionLE I d ∧
    ∀ p : PrimeSpectrum A,
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
                  (ringKrullDim (A ⧸ p.asIdeal)) := sorry

end Ideal.LocalCohomology.AlgebraizationSituation
