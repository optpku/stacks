/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Submodules annihilated by powers of an ideal

The definitions here are independent of schemes and of a chosen presentation
of the ideal.  They provide the torsion submodules and quotient maps used by
ideal-power comparison constructions.
-/

@[expose] public section

noncomputable section

universe u v

namespace Ideal

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- The submodule of elements annihilated by `I ^ n`. -/
abbrev powerAnnihilatedSubmodule (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M]
    (n : ℕ) : Submodule R M :=
  Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)

/-- Membership in the `I ^ n`-annihilated submodule is the corresponding elementwise condition. -/
@[simp]
theorem mem_powerAnnihilatedSubmodule (I : Ideal R) (n : ℕ) (x : M) :
    x ∈ I.powerAnnihilatedSubmodule M n ↔
      ∀ a : R, a ∈ I ^ n → a • x = 0 := sorry

/-- An `I ^ n`-annihilated submodule is zero exactly when its defining elementwise condition
forces an element to vanish. -/
theorem powerAnnihilatedSubmodule_eq_bot_iff (I : Ideal R) (M : Type v)
    [AddCommMonoid M] [Module R M] (n : ℕ) :
    I.powerAnnihilatedSubmodule M n = ⊥ ↔
      ∀ x : M, (∀ a : R, a ∈ I ^ n → a • x = 0) → x = 0 := sorry

/-- The first `I`-annihilated submodule is zero exactly when no nonzero element is annihilated by
every element of `I`. -/
theorem powerAnnihilatedSubmodule_one_eq_bot_iff (I : Ideal R) (M : Type v)
    [AddCommMonoid M] [Module R M] :
    I.powerAnnihilatedSubmodule M 1 = ⊥ ↔
      ∀ x : M, (∀ a : R, a ∈ I → a • x = 0) → x = 0 := sorry

/-- The `I ^ n`-annihilated submodules are monotone in `n`. -/
theorem powerAnnihilatedSubmodule_mono (I : Ideal R) (M : Type v)
    [AddCommMonoid M] [Module R M] {m n : ℕ} (h : m ≤ n) :
    I.powerAnnihilatedSubmodule M m ≤ I.powerAnnihilatedSubmodule M n := sorry

section QuotientMaps

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The quotient map induced by the inclusion of the `I ^ m`-annihilated submodule into the
`I ^ n`-annihilated submodule for `m ≤ n`. -/
noncomputable def powerAnnihilatedSubmoduleQuotientMap (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) :
    M ⧸ I.powerAnnihilatedSubmodule M m →ₗ[R]
      M ⧸ I.powerAnnihilatedSubmodule M n :=
  Submodule.factor (powerAnnihilatedSubmodule_mono I M h)

/-- The ideal-power quotient map sends the class of an element to its class at the later stage. -/
@[simp]
theorem powerAnnihilatedSubmoduleQuotientMap_apply_mkQ (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {m n : ℕ} (h : m ≤ n) (x : M) :
    powerAnnihilatedSubmoduleQuotientMap I M h
        ((I.powerAnnihilatedSubmodule M m).mkQ x) =
      (I.powerAnnihilatedSubmodule M n).mkQ x := sorry

/-- The quotient map between identical ideal-power annihilator stages is the identity. -/
@[simp]
theorem powerAnnihilatedSubmoduleQuotientMap_id (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    I.powerAnnihilatedSubmoduleQuotientMap M (le_refl n) = LinearMap.id := sorry

/-- The quotient maps induced by nested ideal-power annihilator submodules compose as expected. -/
theorem powerAnnihilatedSubmoduleQuotientMap_comp (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {l m n : ℕ} (hlm : l ≤ m) (hmn : m ≤ n) :
    (I.powerAnnihilatedSubmoduleQuotientMap M hmn).comp
        (I.powerAnnihilatedSubmoduleQuotientMap M hlm) =
      I.powerAnnihilatedSubmoduleQuotientMap M (hlm.trans hmn) := sorry

end QuotientMaps


end Ideal
