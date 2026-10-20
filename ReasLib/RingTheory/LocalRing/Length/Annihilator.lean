/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-length modules over local rings

This file provides the local-ring counterpart to
`Module.isFiniteLength_of_pow_smul_top_eq_bot`: a finite-length module is
annihilated by a power of the maximal ideal.

@stack 00IW
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Module

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]

/-- A finite-length module over a local ring is annihilated by a power of the
maximal ideal. -/
@[stacks 00IW "finite-length modules are killed by a maximal-ideal power"]
theorem exists_pow_maximalIdeal_smul_top_eq_bot_of_isFiniteLength
    (hM : IsFiniteLength R M) :
    ∃ n : ℕ, maximalIdeal R ^ n • (⊤ : Submodule R M) = ⊥ := by
  have hfinite := isFiniteLength_iff_isNoetherian_isArtinian.mp hM
  letI : IsNoetherian R M := hfinite.1
  letI : IsArtinian R M := hfinite.2
  let chain : ℕ →o (Submodule R M)ᵒᵈ :=
    ⟨fun n ↦ maximalIdeal R ^ n • (⊤ : Submodule R M),
      fun _ _ h ↦ Submodule.smul_mono_left (Ideal.pow_le_pow_right h)⟩
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes chain
  let N : Submodule R M := maximalIdeal R ^ n • ⊤
  have hN : N = maximalIdeal R • N := by
    change maximalIdeal R ^ n • ⊤ =
      maximalIdeal R • (maximalIdeal R ^ n • ⊤)
    rw [← mul_smul, mul_comm, ← pow_succ]
    exact hn (n + 1) n.le_succ
  refine ⟨n, Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (maximalIdeal R) N (IsNoetherian.noetherian N) hN.le ?_⟩
  exact IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R)

end Module
