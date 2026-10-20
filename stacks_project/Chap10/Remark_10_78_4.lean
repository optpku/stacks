/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.RingTheory.Smooth.Flat
import StacksCheckRecall

/-!
# Remark 10.78.4

The source counterexample is kept as explicit smooth-function-ring data: the
maximal ideal of functions vanishing at zero, the ideal of functions vanishing
near zero, and the canonical equivalence between the resulting quotient and
localization models.

@stack 00NY
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace SmoothRealFunctionCounterexample

/-- The ring `C^∞(ℝ, ℝ)` used in Remark 10.78.4. -/
abbrev FunctionRing := C^∞⟮𝓘(ℝ), ℝ; ℝ⟯

/-- The ideal of smooth functions vanishing at the origin. -/
def vanishingAtZeroIdeal : Ideal FunctionRing :=
  RingHom.ker (ContMDiffMap.evalRingHom (0 : ℝ))

/-- The ideal of smooth functions vanishing on some neighborhood of the origin. Its carrier is
the source formula; only the ideal laws are deferred. -/
def vanishingNearZeroIdeal : Ideal FunctionRing where
  carrier := {f | ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x = 0}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Every smooth function vanishing near zero also vanishes at zero. -/
theorem vanishingNearZeroIdeal_le_vanishingAtZeroIdeal :
    vanishingNearZeroIdeal ≤ vanishingAtZeroIdeal := sorry

/-- The ideal of smooth functions vanishing at zero is maximal. -/
theorem vanishingAtZeroIdeal_isMaximal : vanishingAtZeroIdeal.IsMaximal := sorry

attribute [instance] vanishingAtZeroIdeal_isMaximal

/-- The ideal of smooth functions vanishing at zero is prime. -/
instance vanishingAtZeroIdeal_isPrime : vanishingAtZeroIdeal.IsPrime := sorry

/-- The source localization `R_𝔪`, where `𝔪` consists of functions vanishing at zero. -/
abbrev LocalizationAtZero := Localization.AtPrime vanishingAtZeroIdeal

/-- The quotient `R / I`, where `I` consists of functions vanishing near zero. -/
abbrev QuotientAtZero := FunctionRing ⧸ vanishingNearZeroIdeal

/-- The quotient model is a localization at the complement of the maximal ideal of functions
vanishing at zero. -/
instance quotientAtZeroIsLocalization :
    IsLocalization vanishingAtZeroIdeal.primeCompl QuotientAtZero := sorry

/-- Remark 10.78.4 (1): the localization `R_𝔪` and quotient `R / I` models of the
counterexample are canonically equivalent as `R`-algebras. -/
@[stacks 00NY "(1)"]
noncomputable abbrev localizationEquivQuotient :
    LocalizationAtZero ≃ₐ[FunctionRing] QuotientAtZero :=
  IsLocalization.algEquiv vanishingAtZeroIdeal.primeCompl _ _

/-- Remark 10.78.4 (2): the localization counterexample is a finite module over the smooth
function ring. -/
@[stacks 00NY "(2)"]
instance localizationAtZeroFinite : Module.Finite FunctionRing LocalizationAtZero := sorry

/-- Remark 10.78.4 (3): the localization counterexample is flat over the smooth function ring. -/
@[stacks 00NY "(3)"]
instance localizationAtZeroFlat : Module.Flat FunctionRing LocalizationAtZero := sorry

/-- Remark 10.78.4 (4): the finite flat localization counterexample is not projective. -/
@[stacks 00NY "(4)"]
theorem localizationAtZeroNotProjective :
    ¬ Module.Projective FunctionRing LocalizationAtZero := sorry

#check @localizationEquivQuotient
#check @localizationAtZeroNotProjective

#print axioms vanishingNearZeroIdeal
#print axioms localizationEquivQuotient

end SmoothRealFunctionCounterexample
