/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stability of principal torsion

This leaf owns the module-theoretic condition that the kernel of scalar
multiplication by `a` is unchanged after replacing `a` by `a ^ 2`, together
with the quotient measuring its failure and the annihilator of that quotient.  It also owns the
fixed-cutoff condition that all positive-power torsion has appeared by a specified exponent.

@stack 091X
-/

universe u v

namespace Submodule

variable (R : Type u) (M : Type v)
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Multiplication by `a`-torsion is contained in multiplication by
`a ^ 2`-torsion. -/
theorem torsionBy_le_square (a : R) :
    torsionBy R M a ≤ torsionBy R M (a ^ 2) := sorry

/-- The quotient `M[a ^ 2] / M[a]` measuring the failure of principal
torsion to stabilize after one squaring. -/
@[stacks 07CR "principal torsion step"]
abbrev TorsionStep (a : R) : Type v :=
  torsionBy R M (a ^ 2) ⧸
    (torsionBy R M a).comap (torsionBy R M (a ^ 2)).subtype

namespace TorsionStep

/-- A principal torsion step of a Noetherian module is finite. -/
@[stacks 07CR "finite principal torsion step"]
instance instModuleFinite [IsNoetherian R M] (a : R) :
    Module.Finite R (TorsionStep R M a) := sorry

end TorsionStep

end Submodule

namespace Module

variable (R : Type u) (M : Type v)
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Principal torsion by `a` is stable when the `a`-torsion and
`a ^ 2`-torsion submodules agree. -/
@[stacks 07CR "principal torsion stability"]
def IsTorsionStable (a : R) : Prop :=
  Submodule.torsionBy R M a = Submodule.torsionBy R M (a ^ 2)

/-- All `a`-power torsion is bounded by exponent `c`. -/
@[stacks 091X "bounded principal power torsion at a cutoff"]
def IsPowerTorsionStableAt (a : R) (c : ℕ) : Prop :=
  Submodule.torsion' R M (Submonoid.powers a) =
    Submodule.torsionBy R M (a ^ c)

/-- Bounded `a`-power torsion is equivalent to stability of every finite torsion stage from the
same cutoff onward. -/
@[stacks 091X "bounded principal power torsion criterion"]
theorem isPowerTorsionStableAt_iff (a : R) (c : ℕ) :
    IsPowerTorsionStableAt R M a c ↔
      ∀ m : ℕ, c ≤ m →
        Submodule.torsionBy R M (a ^ m) =
          Submodule.torsionBy R M (a ^ c) := sorry

/-- Principal power torsion in a Noetherian module is bounded at some positive cutoff. -/
@[stacks 091X "Noetherian bounded principal power torsion"]
theorem exists_isPowerTorsionStableAt_of_isNoetherian
    [IsNoetherian R M] (a : R) :
    ∃ c : ℕ+, IsPowerTorsionStableAt R M a c := sorry

/-- Principal torsion stability in its defining submodule form. -/
theorem isTorsionStable_iff (a : R) :
    IsTorsionStable R M a ↔
      Submodule.torsionBy R M a =
        Submodule.torsionBy R M (a ^ 2) := sorry

/-- A scalar acting regularly on a module has stable principal torsion. -/
theorem IsTorsionStable.of_isSMulRegular {a : R}
    (ha : IsSMulRegular M a) : IsTorsionStable R M a := sorry

/-- Stable principal torsion has the same torsion submodule after replacing
the parameter by any positive power. -/
@[stacks 07FE "stable torsion under positive powers"]
theorem IsTorsionStable.torsionBy_pow_eq {a : R}
    (ha : IsTorsionStable R M a) (c : ℕ+) :
    Submodule.torsionBy R M (a ^ (c : ℕ)) =
      Submodule.torsionBy R M a := sorry

/-- Principal torsion stability is preserved by every positive power of the
parameter. -/
@[stacks 07FE "principal torsion stability under positive powers"]
theorem IsTorsionStable.pow {a : R}
    (ha : IsTorsionStable R M a) (c : ℕ+) :
    IsTorsionStable R M (a ^ (c : ℕ)) := sorry

/-- One-step principal torsion stability bounds all power torsion at every positive cutoff. -/
@[stacks 091X "one-step stability implies bounded power torsion"]
theorem IsTorsionStable.isPowerTorsionStableAt {a : R}
    (ha : IsTorsionStable R M a) (c : ℕ+) :
    IsPowerTorsionStableAt R M a c := sorry

/-- Principal torsion is stable exactly when its torsion-step quotient is
subsingleton. -/
theorem isTorsionStable_iff_subsingleton_torsionStep (a : R) :
    IsTorsionStable R M a ↔ Subsingleton (Submodule.TorsionStep R M a) := sorry

/-- The annihilator of the quotient measuring the failure of principal
torsion stability. -/
@[stacks 07CR "principal torsion-step annihilator"]
def torsionStepAnnihilator (a : R) : Ideal R :=
  Module.annihilator R (Submodule.TorsionStep R M a)

/-- The scalar defining a torsion step annihilates that quotient. -/
theorem self_mem_torsionStepAnnihilator (a : R) :
    a ∈ torsionStepAnnihilator R M a := sorry

/-- The torsion-step annihilator is the unit ideal exactly when principal
torsion has stabilized. -/
theorem torsionStepAnnihilator_eq_top_iff (a : R) :
    torsionStepAnnihilator R M a = ⊤ ↔ IsTorsionStable R M a := sorry

/-- For the regular module, principal torsion stability is the usual equality
of the two element-annihilator ideals. -/
theorem isTorsionStable_self_iff_torsionOf (a : R) :
    IsTorsionStable R R a ↔
      Ideal.torsionOf R R a = Ideal.torsionOf R R (a ^ 2) := sorry

end Module
