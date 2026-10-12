/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Derivations compatible with divided powers

This file records the compatibility equation between a derivation and a genuine Mathlib
`DividedPowers` structure. It is independent of a grading: a positive-even ideal in a graded
algebra is one important specialization, not part of the core definition.
-/

@[expose] public section

universe uR uA

namespace DividedPowers

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
variable {I : Ideal A}

/-- At the reusable ideal-theoretic level, a derivation is compatible with divided powers when
`d (gamma.dpow (n + 1) x) = d x * gamma.dpow n x` for every `x` in the divided-power ideal. -/
@[stacks 09PJ "ideal-level divided-power compatible derivations"]
class IsCompatibleWith (gamma : DividedPowers I) (d : Derivation R A A) : Prop where
  /-- The differential of a positive divided power. -/
  d_dpow (n : ℕ) {x : A} (hx : x ∈ I) :
    d (gamma.dpow (n + 1) x) = d x * gamma.dpow n x

namespace IsCompatibleWith

variable {gamma : DividedPowers I} {d : Derivation R A A}

/-- The zero derivation is compatible with every divided-power structure. -/
instance zero (gamma : DividedPowers I) :
    gamma.IsCompatibleWith (0 : Derivation R A A) where
  d_dpow := sorry

/-- Compatibility evaluated at an explicitly positive index. -/
theorem d_dpow_of_pos [h : gamma.IsCompatibleWith d]
    {n : ℕ} (hn : 0 < n) {x : A} (hx : x ∈ I) :
    d (gamma.dpow n x) = d x * gamma.dpow (n - 1) x := sorry

end IsCompatibleWith

/-- The compatibility typeclass is equivalent to its successor-index formula. -/
theorem isCompatibleWith_iff (gamma : DividedPowers I) (d : Derivation R A A) :
    gamma.IsCompatibleWith d ↔
      ∀ (n : ℕ) (x : A), x ∈ I →
        d (gamma.dpow (n + 1) x) = d x * gamma.dpow n x := sorry

/-- The compatibility typeclass is equivalent to the divided-power compatibility formula
at every positive natural index. -/
theorem isCompatibleWith_iff_pos (gamma : DividedPowers I) (d : Derivation R A A) :
    gamma.IsCompatibleWith d ↔
      ∀ (n : ℕ) (x : A), 0 < n → x ∈ I →
        d (gamma.dpow n x) = d x * gamma.dpow (n - 1) x := sorry

end DividedPowers

universe u v w

namespace DividedPowers

/-- For a ring map `f : A →+* B` and divided powers `δ` on an ideal `J` of `B`,
a divided-power `A`-derivation into a `B`-module `M` is an additive Leibniz map
that vanishes on `f A` and satisfies the divided-power compatibility formula. -/
structure DividedPowerDerivation
    {A : Type u} [CommRing A] {B : Type v} [CommRing B]
    {J : Ideal B} (f : A →+* B) (δ : DividedPowers J)
    (M : Type w) [AddCommGroup M] [Module B M]
    extends Derivation ℤ B M where
  /-- The derivation vanishes on the image of the base ring map. -/
  map_base : ∀ a : A, toDerivation (f a) = 0
  /-- The derivation satisfies the divided-power compatibility formula on `J`. -/
  map_dpow : ∀ (n : ℕ+) {x : B}, x ∈ J →
    toDerivation (δ.dpow (n : ℕ) x) =
      δ.dpow ((n : ℕ) - 1) x • toDerivation x

namespace DividedPowerDerivation

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]
variable {J : Ideal B} (f : A →+* B) (δ : DividedPowers J)
variable (M : Type w) [AddCommGroup M] [Module B M]

/-- Construct a divided-power derivation from an ordinary derivation that vanishes
on the base ring and satisfies the divided-power compatibility formula. -/
def of (D : Derivation ℤ B M)
    (h_base : ∀ a : A, D (f a) = 0)
    (h_dpow : ∀ (n : ℕ+) {x : B}, x ∈ J →
      D (δ.dpow (n : ℕ) x) = δ.dpow ((n : ℕ) - 1) x • D x) :
    DividedPowerDerivation f δ M :=
  { toDerivation := D
    map_base := h_base
    map_dpow := h_dpow }

variable {f δ M}

/-- Evaluate a divided-power derivation on an element of its source ring. -/
def apply (D : DividedPowerDerivation f δ M) : B → M :=
  fun b ↦ D.toDerivation b

/-- A divided-power derivation vanishes on the base ring and satisfies divided-power
compatibility at every positive natural index on the divided-power ideal. -/
theorem spec (D : DividedPowerDerivation f δ M) :
    (∀ a : A, D.apply (f a) = 0) ∧
      (∀ (n : ℕ) (x : B), 0 < n → x ∈ J →
        D.apply (δ.dpow n x) = δ.dpow (n - 1) x • D.apply x) := sorry

/-- Two divided-power derivations are equal when their underlying maps agree pointwise. -/
theorem ext {D₁ D₂ : DividedPowerDerivation f δ M}
    (h : ∀ b : B, D₁.apply b = D₂.apply b) : D₁ = D₂ := sorry

end DividedPowerDerivation

end DividedPowers
