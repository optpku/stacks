/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.Maximal
public import ReasLib.RingTheory.Depth.Equiv
public import ReasLib.RingTheory.Depth.Exact
public import ReasLib.RingTheory.Depth.SupportDim

/-!
# Depth bounds for Cohen--Macaulay local rings

This leaf collects the reusable dimension and finite-free consequences of a local
Cohen--Macaulay hypothesis.  The statements are phrased for arbitrary module universes and live
under the `Module` owner namespace; chapter entries should use these facts instead of rebuilding
support-dimension arguments and finite-basis transports privately.

@stack 00NE
@stack 00NG
@stack 00NF
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A Cohen--Macaulay local ring is nontrivial. -/
@[stacks 00NE "Cohen--Macaulay local ring is nontrivial", stacks 00NG "Cohen--Macaulay local ring is nontrivial"]
theorem CohenMacaulay.nontrivial (hCM : CohenMacaulay R R) : Nontrivial R := sorry

/-- A Cohen--Macaulay self-module has depth equal to the Krull dimension of its ring.

This is the dimension-free owner theorem; the numbered `d` form below is a source-facing
specialization for arguments that have already named the dimension. -/
@[stacks 00NE "depth equals ring dimension for a Cohen--Macaulay self-module",
  stacks 00NG "depth equals ring dimension for a Cohen--Macaulay self-module"]
theorem CohenMacaulay.moduleDepth_eq_ringKrullDim
    (hCM : CohenMacaulay R R) :
    WithBot.some (moduleDepth R R) = ringKrullDim R := sorry

/-- The depth of the self-module of a Cohen--Macaulay local ring is its Krull dimension. -/
@[stacks 00NE "depth of a Cohen--Macaulay self-module", stacks 00NG "depth of a Cohen--Macaulay self-module"]
theorem moduleDepth_self_eq_ringKrullDim {d : ℕ}
    (hCM : CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R R = d := sorry

/-- The depth of a finite nonempty power of a Cohen--Macaulay local ring is its Krull dimension. -/
@[stacks 00NE "depth of a finite power of the ring", stacks 00NG "depth of a finite power of the ring"]
theorem moduleDepth_pi_eq_ringKrullDim {ι : Type v} [Finite ι] [Nonempty ι] {d : ℕ}
    (hCM : CohenMacaulay R R) (hdim : ringKrullDim R = d) :
    moduleDepth R (ι → R) = d := sorry

/-- A finite nonempty power of a Cohen--Macaulay ring has full depth in `WithBot ℕ∞` form. -/
@[stacks 00NE "finite power depth and ring dimension", stacks 00NG "finite power depth and ring dimension"]
theorem CohenMacaulay.moduleDepth_pi_eq_ringKrullDim
    {ι : Type v} [Finite ι] [Nonempty ι] (hCM : CohenMacaulay R R) :
    (moduleDepth R (ι → R) : WithBot ℕ∞) = ringKrullDim R := sorry

/-- A nontrivial finite module has depth at most the ambient ring dimension. -/
@[stacks 00NE "depth upper bound by ring dimension", stacks 00NG "depth upper bound by ring dimension"]
theorem moduleDepth_le_ringKrullDim_of_nontrivial
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M]
    {d : ℕ} (hdim : ringKrullDim R = d) :
    moduleDepth R M ≤ d := sorry

/-- A nontrivial finite free module over a Cohen--Macaulay local ring has full depth. -/
@[stacks 00NE "depth of a nontrivial finite free module", stacks 00NG "depth of a nontrivial finite free module"]
theorem moduleDepth_eq_ringKrullDim_of_nontrivial_finite_free
    {P : Type v} [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    [Nontrivial P] {d : ℕ} (hCM : CohenMacaulay R R)
    (hdim : ringKrullDim R = d) :
    moduleDepth R P = d := sorry

/-- A finite module whose depth equals the ring dimension is maximal Cohen--Macaulay. -/
@[stacks 00NE "full-depth module is maximal Cohen--Macaulay", stacks 00NG "full-depth module is maximal Cohen--Macaulay"]
theorem maximalCohenMacaulay_of_moduleDepth_eq_ringKrullDim
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {d : ℕ} (hdim : ringKrullDim R = d) (hdepth : moduleDepth R M = d) :
    MaximalCohenMacaulay R M := sorry

namespace MaximalCohenMacaulay

/-- Construct the maximal Cohen--Macaulay owner directly from its depth equation.

The equality is written in the ambient `WithBot ℕ∞` type used by the structure field, so this
constructor does not force callers to introduce an artificial natural-number dimension. -/
@[stacks 00NF "construct a maximal Cohen--Macaulay module from full depth"]
theorem of_moduleDepth_eq_ringKrullDim
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hdepth : WithBot.some (moduleDepth R M) = ringKrullDim R) :
    MaximalCohenMacaulay R M := sorry

end MaximalCohenMacaulay

end Module
