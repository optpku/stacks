/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.Quotient.BaseIdeal
public import ReasLib.RingTheory.Ideal.Quotient.Prime
public import ReasLib.RingTheory.Sequence.Annihilator
public import ReasLib.RingTheory.Smooth.Resolution.AtPrime
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected

@[expose] public section

/-!
# Lifting resolutions through finite power quotients

This file provides the eighth-power lifting theorem for resolutions.
-/

universe u v w

namespace AlgHom.ResolvableAtPrime

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ]

/-- Lemma 16.9.2 (Tag 07F8): a resolution modulo the eighth powers of a
finite base family lifts when successive annihilators stabilize in the base
and target and every family member is strictly standard in the source. -/
@[stacks 07F8]
theorem of_eighthPowerSpan
    [IsNoetherianRing R] [Algebra.FinitePresentation R A]
    (φ : A →ₐ[R] Λ) (q : PrimeSpectrum Λ)
    {r : ℕ} (π : Fin r → R)
    (hπ : ∀ i, algebraMap R Λ (π i) ∈ q.asIdeal)
    (hAnnR : RingTheory.Sequence.StableAnnihilators π 8)
    (hAnnTarget : RingTheory.Sequence.StableAnnihilators
      (fun i ↦ algebraMap R Λ (π i)) 8)
    (hStrict : ∀ i, Algebra.IsStrictlyStandard R (algebraMap R A (π i)))
    (hresolve :
      (φ.quotientByBaseIdeal (Ideal.finPowerSpan π 8)).ResolvableAtPrime
        (PrimeSpectrum.PowerSpan.quotient
          (algebraMap R Λ) q π 8 hπ)) :
    φ.ResolvableAtPrime q := sorry

end AlgHom.ResolvableAtPrime
