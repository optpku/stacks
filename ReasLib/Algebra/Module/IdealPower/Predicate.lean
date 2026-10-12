/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Data.PNat.Basic
public import ReasLib.Algebra.Module.IdealPower.Torsion
public import ReasLib.Algebra.Module.IdealPower.Submodule
public import ReasLib.RingTheory.Ideal.Principal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Modules supported on powers of an ideal

The finite stages are owned by `Ideal.powerAnnihilatedSubmodule` in the sibling
torsion leaf.  The union of those stages is Mathlib's `Ideal.primaryComponent`;
this file only packages the corresponding module predicate and its small,
reusable closure and principal-element bridges.

The fixed-power and unbounded-power submodules are exposed through explicit declarations rather
than competing notation.
-/

@[expose] public section

noncomputable section

universe u v w z

namespace Ideal

variable {R : Type u} [CommSemiring R]

/-- The finite `I`-power-torsion stage, named through the canonical
`Ideal.powerAnnihilatedSubmodule` construction. -/
@[stacks 05E6 "finite ideal-power torsion stage"]
abbrev powerTorsion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ) :
    Submodule R M :=
  I.powerAnnihilatedSubmodule M n

end Ideal

namespace Module

open scoped DirectSum

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- A module is annihilated by a power of `I` when one exponent works uniformly for all
elements. -/
@[stacks 0927 "module annihilated by an ideal power"]
def IsAnnihilatedByPower
    (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop :=
  ∃ n : ℕ, I ^ n ≤ Module.annihilator R M

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- An ideal power annihilates a module exactly when the corresponding adic stage is zero. -/
@[stacks 0927 "ideal-power annihilation stage criterion"]
theorem pow_le_annihilator_iff_stage_eq_bot (I : Ideal R) (n : ℕ) :
    I ^ n ≤ Module.annihilator R M ↔
      Ideal.PowerSubmodule.stage I M n = ⊥ := sorry
-- Proof strategy: unfold the annihilator and `Ideal.PowerSubmodule.stage`, then compare
-- membership elementwise using `Submodule.eq_bot_iff`.

/-- Uniform annihilation is equivalently the vanishing of one adic submodule stage. -/
@[stacks 0927 "uniform ideal-power annihilation stage criterion"]
theorem isAnnihilatedByPower_iff_exists_stage (I : Ideal R) :
    IsAnnihilatedByPower I M ↔
      ∃ n : ℕ, Ideal.PowerSubmodule.stage I M n = ⊥ := sorry
-- Proof strategy: unfold `IsAnnihilatedByPower` and apply
-- `pow_le_annihilator_iff_stage_eq_bot` under the existential quantifier.

end CommSemiring

section CommRing

variable {R : Type u} [CommRing R]

/-- A module is power torsion for an ideal when its canonical primary component is the whole
module.

The primary-component formulation is the canonical owner; the elementwise
positive-exponent formulation is exposed by `isIdealPowerTorsion_iff` below. -/
@[stacks 05E6 "Definition 15.89.1 (1), ideal-power torsion module"]
abbrev IsIdealPowerTorsion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop :=
  Ideal.primaryComponent M I = ⊤

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- A module annihilated by one ideal power is ideal-power torsion. -/
@[stacks 0927 "bounded ideal-power torsion implies power torsion"]
theorem IsAnnihilatedByPower.isIdealPowerTorsion
    {I : Ideal R} (h : IsAnnihilatedByPower I M) : IsIdealPowerTorsion I M := sorry
-- Proof strategy: choose the uniform exponent from `h` and show every element belongs to
-- the corresponding stage of `Ideal.primaryComponent`.

/-- The primary-component predicate is equivalent to exhaustion by finite
`I`-annihilated stages, in the ambient elementwise form. -/
@[stacks 05E6 "exhaustion by finite ideal-power torsion stages"]
theorem isIdealPowerTorsion_iff_exists_stage (I : Ideal R) :
    IsIdealPowerTorsion I M ↔
      ∀ x : M, ∃ n : ℕ, x ∈ I.powerAnnihilatedSubmodule M n := sorry
-- Proof strategy: unfold `IsIdealPowerTorsion` and `Ideal.primaryComponent`, then rewrite
-- membership in the supremum of the increasing finite stages.

/-- Ideal-power torsion is equivalently the elementwise condition using positive exponents. -/
@[stacks 05E6 "Definition 15.89.1 (1), elementwise criterion"]
theorem isIdealPowerTorsion_iff (I : Ideal R) :
    IsIdealPowerTorsion I M ↔
      ∀ x : M, ∃ n : ℕ+, ∀ a : R, a ∈ I ^ (n : ℕ) → a • x = 0 := sorry
-- Proof strategy: start from `isIdealPowerTorsion_iff_exists_stage`, translate stage
-- membership with `Submodule.mem_torsionBySet_iff`, and replace a natural witness by a
-- positive one using monotonicity of ideal powers.

/-- The finite quotient `R ⧸ I^n` is `I`-power torsion. -/
@[stacks 05E6 "ideal-power torsion of finite power quotients"]
theorem isIdealPowerTorsion_quotient_pow (I : Ideal R) (n : ℕ) :
    IsIdealPowerTorsion I (R ⧸ (I ^ n)) := sorry
-- Proof strategy: use the bounded-torsion criterion with exponent `n`; every element of
-- `I ^ n` acts trivially on the quotient.

/-- `I`-power torsion is invariant under a linear equivalence. -/
@[stacks 05E6 "ideal-power torsion under linear equivalence"]
theorem isIdealPowerTorsion_iff_of_linearEquiv
    (I : Ideal R) {N : Type w} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) :
    IsIdealPowerTorsion I M ↔ IsIdealPowerTorsion I N := sorry
-- Proof strategy: apply the elementwise criterion in both directions and transport each
-- annihilation equation through `e` or `e.symm`.

/-- A direct sum of modules supported on powers of `I` is again supported on
powers of `I`. -/
@[stacks 05E6 "ideal-power torsion of direct sums"]
theorem isIdealPowerTorsion_directSum
    (I : Ideal R) {ι : Type w} {A : ι → Type z}
    [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    (hA : ∀ i, IsIdealPowerTorsion I (A i)) :
    IsIdealPowerTorsion I (⨁ i, A i) := sorry
-- Proof strategy: use finite support of a direct-sum element, choose one exponent for each
-- occupied component, and take a common upper bound before applying the elementwise criterion.

/-- The primary component for a principal ideal agrees with Mathlib's
`Submodule.torsion'` by the corresponding powers submonoid. -/
@[stacks 05E6 "principal ideal primary component"]
theorem primaryComponent_principalIdeal_eq_fPowerTorsion (f : R) :
    Ideal.primaryComponent M (principalIdeal f) =
      Submodule.torsion' R M (Submonoid.powers f) := sorry
-- Proof strategy: ext an element and identify membership in a principal ideal power with
-- annihilation by a sufficiently large power of `f`.

/-- For a principal ideal, ideal-power torsion is the canonical powers-submonoid torsion
predicate. -/
@[stacks 05E6 "Definition 15.89.1 (2), element-power torsion module"]
theorem isIdealPowerTorsion_principalIdeal_iff (f : R) :
    IsIdealPowerTorsion (principalIdeal f) M ↔
      IsTorsion' M (Submonoid.powers f) := sorry
-- Proof strategy: unfold both predicates and rewrite the primary component using
-- `primaryComponent_principalIdeal_eq_fPowerTorsion`.

end CommRing



end Module

end
