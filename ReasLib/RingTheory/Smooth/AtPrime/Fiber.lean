/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.EssentialFiniteness.AtPrime
public import ReasLib.RingTheory.RingHom.Fiber.Local
public import ReasLib.RingTheory.Smooth.AtPrime

@[expose] public section

/-!
# Smoothness at a Prime from the Fiber

The general ring-hom pointwise predicates for finite presentation and
flatness remain in `RingHom.Local.AtPrime`.  This leaf packages their
algebra-side use with the canonical fiber point selected by a target prime.

@stack 00TF
-/

universe u v

namespace Algebra.SmoothAtPrime

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The finite-presentation, local-flatness, and canonical-fiber-smoothness
conditions at a target prime. -/
@[stacks 00TF "local smooth-fiber criterion"]
def FiberCriterion (q : PrimeSpectrum S) : Prop :=
  Algebra.FinitePresentationAt R S q ∧
    (algebraMap R S).FlatAt q ∧
      Algebra.SmoothAtPrime (q.asIdeal.under R).ResidueField
        ((q.asIdeal.under R).Fiber S) (fiberPrimeAt R S q)

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.137.16 (Stacks 00TF): the local smooth-fiber criterion makes the
algebra smooth on a principal-open neighborhood of the target prime. -/
@[stacks 00TF "smoothness at a prime from a local smooth fiber"]
theorem of_fiberCriterion {q : PrimeSpectrum S} (h : FiberCriterion R S q) :
    Algebra.SmoothAtPrime R S q := sorry

/-- A source-style constructor for smoothness at a prime.  Prefer
`of_fiberCriterion` when the three hypotheses are reused as one condition. -/
@[stacks 00TF "smoothness at a prime from a local smooth fiber"]
theorem of_fiber (q : PrimeSpectrum S)
    (hfp : ∃ g : S, g ∉ q.asIdeal ∧ Algebra.FinitePresentation R (Localization.Away g))
    (hflat :
      (Localization.localRingHom (q.asIdeal.under R) q.asIdeal (algebraMap R S) rfl).Flat)
    (hfiber :
      Algebra.SmoothAtPrime (q.asIdeal.under R).ResidueField
        ((q.asIdeal.under R).Fiber S) (fiberPrimeAt R S q)) :
    Algebra.SmoothAtPrime R S q := sorry

end Algebra.SmoothAtPrime
