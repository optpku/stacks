/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.Transport
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.Hypotheses

open CategoryTheory
open Ideal.LocalCohomology

universe u v

/- Lemma 52.10.3 (1): shrinking a specialization-stable subset preserves the
algebraization situation. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.restrict :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (T' : Set (PrimeSpectrum A))
      (hT' : StableUnderSpecialization T') (hsub : T' ⊆ T),
      AlgebraizationSituation C I M T' s d)

/- Lemma 52.10.3 (2): localization carries an algebraization situation to the
localized ring, mapped ideal, localized module, and inverse-image support. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.localize :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (S : Submonoid A)
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} (Localization S)))]
      (Cs : CategoryTheory.DerivedCategory.CanonicalClosedPresentation
        (A := Localization S)),
      AlgebraizationSituation Cs
        (I.map (algebraMap A (Localization S)))
        (LocalizedModule S M)
        {q : PrimeSpectrum (Localization S) |
          PrimeSpectrum.comap (algebraMap A (Localization S)) q ∈ T} s d)

/- Lemma 52.10.3 (3): I-adic completion carries an algebraization situation
to the completed ring, mapped ideal, completed module, and inverse-image support. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.complete :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      [MonoidalCategory
        (DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))]
      (Chat : CategoryTheory.DerivedCategory.CanonicalClosedPresentation
        (A := AdicCompletion I A)),
      AlgebraizationSituation Chat
        (I.map (algebraMap A (AdicCompletion I A)))
        (AdicCompletion I M)
        {q : PrimeSpectrum (AdicCompletion I A) |
          PrimeSpectrum.comap (algebraMap A (AdicCompletion I A)) q ∈ T} s d)

/- Lemma 52.10.3 (4): under the Jacobson-radical hypothesis, the dimension and
depth assumptions required by Lemma 52.8.2 follow for `I` and `a`. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.stabilizationHypotheses :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (a : Ideal A) (hIa : I ≤ a)
      (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
      (hJac : I ≤ Ring.jacobson A),
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
                        (ringKrullDim (p.asIdeal.quotientAtPrime q))))

/- Lemma 52.10.3 (5): with the same Jacobson-radical hypothesis, the strict
depth condition needed by Lemma 52.8.4 also follows. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.stabilizationDepthHypotheses :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (a : Ideal A) (hIa : I ≤ a)
      (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
      (hJac : I ≤ Ring.jacobson A),
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
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)))

/- Lemma 52.10.3 (6): when `A` is `I`-adically complete, the hypotheses of
Lemma 52.8.5 other than its possible condition (5) are available. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.derivedCompletionHypotheses :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (a : Ideal A) (hIa : I ≤ a)
      (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
      [IsAdicComplete I A],
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
                        (ringKrullDim (p.asIdeal.quotientAtPrime q)))

/- Lemma 52.10.3 (7): in the local case with maximal ideal `a`, the hypotheses
of Lemma 52.9.2 are satisfied. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.localStabilizationHypotheses :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (a : Ideal A) (hIa : I ≤ a)
      (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
      (hmax : IsLocalRing.maximalIdeal A = a),
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
                    (ringKrullDim (A ⧸ p.asIdeal))))

/- Lemma 52.10.3 (8): in the local case with maximal ideal `a`, the strict
depth hypotheses of Lemma 52.9.4 are satisfied as well. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.localDepthHypotheses :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (a : Ideal A) (hIa : I ≤ a)
      (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
      (hmax : IsLocalRing.maximalIdeal A = a),
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
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt)))

/- Lemma 52.10.3 (9): in the local `I`-adically complete case, the dimension
and depth hypotheses of Lemma 52.9.5 are satisfied. -/
@[stacks 0EFV] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.localDerivedCompletionHypotheses :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      [IsLocalRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (C : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      {I : Ideal A} {T : Set (PrimeSpectrum A)} {s d : ℤ}
      (h : AlgebraizationSituation C I M T s d)
      (a : Ideal A) (hIa : I ≤ a)
      (hV : PrimeSpectrum.zeroLocus (a : Set A) ⊆ T)
      (hmax : IsLocalRing.maximalIdeal A = a)
      [IsAdicComplete I A],
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
                    (ringKrullDim (A ⧸ p.asIdeal)))
