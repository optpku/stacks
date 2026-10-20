/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.CompleteTarget
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex

/-!
# Exactness after completion with a complete target

@stack 0BNG

The target-side maps are expressed through the canonical `mapToComplete` and
`mapToPowSmulTopEqBot` owners.  The reusable complete-target theorem and its
power-annihilated source specialization live together without exposing a local
completeness instance to consumers.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace AdicCompletion

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {M N Q : Type v}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q]

/-- The completed target map has zero composite when the original linear maps
form an exact pair.  Keeping this as a named Prop bridge lets the short-complex
constructor remain a concrete expression in the public theorem below. -/
@[stacks 0BNG "zero composite for a completed exact pair"]
theorem mapToComplete_comp_eq_zero_of_exact
    [IsAdicComplete I Q] {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hfg : Function.Exact f g) :
    (mapToComplete I g).comp ((AdicCompletion.map I f).restrictScalars R) = 0 := sorry

/-- Lemma 10.96.4 (0BNG): an exact, injective, and surjective linear sequence
remains short exact after `I`-adic completion when its target is already
`I`-adically complete.  The target map is the canonical `mapToComplete` map;
`completion_shortExact_of_pow_smul_top_eq_bot` supplies the source specialization. -/
@[stacks 0BNG "completed short exact sequence with complete target"]
theorem completion_shortExact_of_complete_target
    [IsAdicComplete I Q] {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    (ShortComplex.moduleCatMk
      ((AdicCompletion.map I f).restrictScalars R)
      (mapToComplete I g)
      (mapToComplete_comp_eq_zero_of_exact I hfg)).ShortExact := sorry

/-- The map to a power-annihilated target has zero composite with the completed first map when
the original pair is exact. -/
@[stacks 0BNG "zero composite for a power-annihilated target"]
theorem mapToPowSmulTopEqBot_comp_eq_zero_of_exact
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    (mapToPowSmulTopEqBot I g hc).comp
      ((AdicCompletion.map I f).restrictScalars R) = 0 := sorry

/-- Lemma 10.96.4 (0BNG): if an exact linear sequence has injective first map, surjective second
map, and target annihilated by a power of `I`, then completing its first two terms gives a short
exact sequence. -/
@[stacks 0BNG]
theorem completion_shortExact_of_pow_smul_top_eq_bot
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q}
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)
    {c : ℕ} (hc : I ^ c • (⊤ : Submodule R Q) = ⊥) :
    (ShortComplex.moduleCatMk
      ((AdicCompletion.map I f).restrictScalars R)
      (mapToPowSmulTopEqBot I g hc)
      (mapToPowSmulTopEqBot_comp_eq_zero_of_exact I hfg hc)).ShortExact := sorry

end AdicCompletion
