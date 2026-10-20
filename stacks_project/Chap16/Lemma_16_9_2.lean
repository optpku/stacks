/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Resolution.Quotient

@[expose] public section

universe u v w

/- Lemma 16.9.2: resolution lifts through the quotient by eighth powers of a
finite base family under the successive-annihilator and strict-standardness
hypotheses. -/
@[stacks 07F8] #check
  fun {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ]
    [Algebra R A] [Algebra R Λ]
    [IsNoetherianRing R] [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    (r : ℕ+) (π : Fin r → R)
    (hπ : ∀ i, algebraMap R Λ (π i) ∈ q.asIdeal)
    (hAnnR : RingTheory.Sequence.StableAnnihilators π 8)
    (hAnnTarget : RingTheory.Sequence.StableAnnihilators
      (fun i ↦ algebraMap R Λ (π i)) 8)
    (hStrict : ∀ i, Algebra.IsStrictlyStandard R (algebraMap R A (π i)))
    (hresolve :
      (φ.quotientByBaseIdeal (Ideal.finPowerSpan π 8)).ResolvableAtPrime
        (PrimeSpectrum.PowerSpan.quotient
          (algebraMap R Λ) q π 8 hπ)) ↦
      AlgHom.ResolvableAtPrime.of_eighthPowerSpan
        φ q π hπ hAnnR hAnnTarget hStrict hresolve

#check @AlgHom.ResolvableAtPrime.of_eighthPowerSpan

#check @Ideal.finPowerSpan
#check @Ideal.finPrefixPowerSpan
#check @Ideal.map_finPrefixPowerSpan
#check @RingTheory.Sequence.PrefixPowerQuotient
#check @RingTheory.Sequence.prefixQuotientClass
#check @RingTheory.Sequence.StableAnnihilator
#check @RingTheory.Sequence.StableAnnihilators
#check @PrimeSpectrum.PowerSpan.quotient
