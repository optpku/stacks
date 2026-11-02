/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
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
open scoped Topology

namespace SmoothRealFunctionCounterexample

/-- The ring `C^∞(ℝ, ℝ)` used in Remark 10.78.4. -/
abbrev FunctionRing := C^∞⟮𝓘(ℝ), ℝ; ℝ⟯

/-- The ideal of smooth functions vanishing at the origin. -/
def vanishingAtZeroIdeal : Ideal FunctionRing :=
  RingHom.ker (ContMDiffMap.evalRingHom (0 : ℝ))

/-- The ideal of smooth functions vanishing on some neighborhood of the origin. -/
def vanishingNearZeroIdeal : Ideal FunctionRing where
  carrier := {f | ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x = 0}
  zero_mem' := ⟨1, zero_lt_one, by intro x hx; rfl⟩
  add_mem' := by
    rintro f g ⟨ε, hε, hf⟩ ⟨δ, hδ, hg⟩
    refine ⟨min ε δ, lt_min hε hδ, ?_⟩
    intro x hx
    change f x + g x = 0
    rw [hf x (lt_of_lt_of_le hx (min_le_left _ _)),
      hg x (lt_of_lt_of_le hx (min_le_right _ _)), add_zero]
  smul_mem' := by
    rintro f g ⟨ε, hε, hg⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx
    change f x * g x = 0
    rw [hg x hx, mul_zero]

/-- Membership in the source ideal means equality to zero as a germ at the origin. -/
theorem mem_vanishingNearZeroIdeal_iff (f : FunctionRing) :
    f ∈ vanishingNearZeroIdeal ↔ ∀ᶠ x in 𝓝 (0 : ℝ), f x = 0 := by
  change (∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x = 0) ↔ _
  simp only [Metric.eventually_nhds_iff, Real.dist_eq, sub_zero]

/-- Every smooth function vanishing near zero also vanishes at zero. -/
theorem vanishingNearZeroIdeal_le_vanishingAtZeroIdeal :
    vanishingNearZeroIdeal ≤ vanishingAtZeroIdeal := by
  rintro f ⟨ε, hε, hf⟩
  exact hf 0 (by simpa using hε)

/-- The ideal of smooth functions vanishing at zero is maximal. -/
theorem vanishingAtZeroIdeal_isMaximal : vanishingAtZeroIdeal.IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro x
  exact ⟨ContMDiffMap.const x, rfl⟩

attribute [instance] vanishingAtZeroIdeal_isMaximal

/-- The ideal of smooth functions vanishing at zero is prime. -/
instance vanishingAtZeroIdeal_isPrime : vanishingAtZeroIdeal.IsPrime :=
  vanishingAtZeroIdeal_isMaximal.isPrime

/-- The source localization `R_𝔪`, where `𝔪` consists of functions vanishing at zero. -/
abbrev LocalizationAtZero := Localization.AtPrime vanishingAtZeroIdeal

/-- The quotient `R / I`, where `I` consists of functions vanishing near zero. -/
abbrev QuotientAtZero := FunctionRing ⧸ vanishingNearZeroIdeal

/-- A function nonzero at the origin has a globally smooth representative of its inverse germ.
The denominator is regularized away from the support of a bump function. -/
theorem exists_inverse_germ (f : FunctionRing) (hf : f 0 ≠ 0) :
    ∃ g : FunctionRing, ∀ᶠ x in 𝓝 (0 : ℝ), f x * g x = 1 := by
  let b : ContDiffBump (f 0) :=
    ⟨|f 0| / 4, |f 0| / 2, by positivity, by
      have := abs_pos.mpr hf
      linarith⟩
  have hb0 : b (0 : ℝ) = 0 := by
    apply b.zero_of_le_dist
    change |f 0| / 2 ≤ dist 0 (f 0)
    rw [Real.dist_eq, zero_sub, abs_neg]
    linarith [abs_nonneg (f 0)]
  have hd (t : ℝ) : t ^ 2 + (1 - b t) ^ 2 ≠ 0 := by
    by_cases ht : t = 0
    · simp [ht, hb0]
    · have := sq_pos_of_ne_zero ht
      have := sq_nonneg (1 - b t)
      positivity
  have hfd : ContDiff ℝ ∞ f := f.contMDiff.contDiff
  let g : FunctionRing := ⟨fun x => f x / ((f x) ^ 2 + (1 - b (f x)) ^ 2),
    (hfd.div ((hfd.pow 2).add
      ((contDiff_const.sub (b.contDiff.comp hfd)).pow 2)) (fun x => hd (f x))).contMDiff⟩
  refine ⟨g, ?_⟩
  have hb : ∀ᶠ x in 𝓝 (0 : ℝ), b (f x) = 1 :=
    f.contMDiff.continuous.continuousAt.eventually b.eventuallyEq_one
  filter_upwards [hb] with x hx
  have hfx : f x ≠ 0 := by
    intro h
    rw [h, hb0] at hx
    exact zero_ne_one hx
  change f x * (f x / ((f x) ^ 2 + (1 - b (f x)) ^ 2)) = 1
  rw [hx]
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [← mul_div_assoc, ← pow_two, div_self (pow_ne_zero _ hfx)]

/-- A bump function equal to one at the origin annihilates any function vanishing near it. -/
theorem exists_annihilator (f : FunctionRing) (hf : f ∈ vanishingNearZeroIdeal) :
    ∃ s : FunctionRing, s 0 = 1 ∧ s * f = 0 := by
  obtain ⟨ε, hε, hf⟩ := hf
  let b : ContDiffBump (0 : ℝ) :=
    ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  refine ⟨⟨b, b.contDiff.contMDiff⟩,
    b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), ?_⟩
  ext x
  change b x * f x = 0
  by_cases hx : |x| < ε
  · rw [hf x hx, mul_zero]
  · have hb : b x = 0 := b.zero_of_le_dist (by
      simpa only [Real.dist_eq, sub_zero] using le_of_not_gt hx)
    rw [hb, zero_mul]

/-- The quotient model is a localization at the complement of the maximal ideal of functions
vanishing at zero. -/
instance quotientAtZeroIsLocalization :
    IsLocalization vanishingAtZeroIdeal.primeCompl QuotientAtZero := by
  rw [isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have hs : (s : FunctionRing) 0 ≠ 0 := s.property
    obtain ⟨g, hg⟩ := exists_inverse_germ s hs
    apply isUnit_iff_exists_inv.mpr
    refine ⟨Ideal.Quotient.mk _ g, ?_⟩
    change Ideal.Quotient.mk vanishingNearZeroIdeal s *
      Ideal.Quotient.mk vanishingNearZeroIdeal g = 1
    rw [← map_mul, Ideal.Quotient.mk_eq_one_iff_sub_mem,
      mem_vanishingNearZeroIdeal_iff]
    filter_upwards [hg] with x hx
    change (s : FunctionRing) x * g x - 1 = 0
    rw [hx, sub_self]
  · intro z
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨(f, 1), by simp⟩
  · intro f g hfg
    have hmem : f - g ∈ vanishingNearZeroIdeal := (Ideal.Quotient.eq).mp hfg
    obtain ⟨s, hs, hsf⟩ := exists_annihilator (f - g) hmem
    refine ⟨⟨s, ?_⟩, ?_⟩
    · change s 0 ≠ 0
      rw [hs]
      exact one_ne_zero
    · exact sub_eq_zero.mp (by simpa only [mul_sub] using hsf)

/-- Remark 10.78.4 (1): the localization `R_𝔪` and quotient `R / I` models of the
counterexample are canonically equivalent as `R`-algebras. -/
@[stacks 00NY "(1)"]
noncomputable abbrev localizationEquivQuotient :
    LocalizationAtZero ≃ₐ[FunctionRing] QuotientAtZero :=
  IsLocalization.algEquiv vanishingAtZeroIdeal.primeCompl _ _

/-- Remark 10.78.4 (2): the localization counterexample is a finite module over the smooth
function ring. -/
@[stacks 00NY "(2)"]
instance localizationAtZeroFinite : Module.Finite FunctionRing LocalizationAtZero :=
  Module.Finite.equiv localizationEquivQuotient.symm.toLinearEquiv

/-- Remark 10.78.4 (3): the localization counterexample is flat over the smooth function ring. -/
@[stacks 00NY "(3)"]
instance localizationAtZeroFlat : Module.Flat FunctionRing LocalizationAtZero :=
  IsLocalization.flat _ vanishingAtZeroIdeal.primeCompl

/-- Remark 10.78.4 (4): the finite flat localization counterexample is not projective. -/
@[stacks 00NY "(4)"]
theorem localizationAtZeroNotProjective :
    ¬ Module.Projective FunctionRing LocalizationAtZero := sorry

#check @localizationEquivQuotient
#check @localizationAtZeroNotProjective

#print axioms vanishingNearZeroIdeal
#print axioms localizationEquivQuotient

end SmoothRealFunctionCounterexample
