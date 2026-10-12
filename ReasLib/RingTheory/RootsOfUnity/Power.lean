/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Power maps between roots of unity

The divisibility map `μₙ(R) → μₘ(R)` is obtained by raising a unit to `n / m`.
The map is kept separate from any field- or ramification-specific argument so that tower
comparisons can use it directly.

@stack 0BU7
-/

universe u

namespace rootsOfUnity

variable {R : Type u} [CommMonoid R] {m n k : ℕ}

/-- The powered unit is an `m`th root of unity when `m ∣ n` and the source is an `n`th root. -/
@[stacks 0BU7 "power map membership for roots of unity"]
theorem powMap_mem (h : m ∣ n) (ζ : rootsOfUnity n R) :
    (ζ : Units R) ^ (n / m) ∈ rootsOfUnity m R := sorry

/-- Raising roots of unity to the quotient exponent preserves the identity. -/
@[stacks 0BU7 "power map identity law for roots of unity"]
theorem powMap_one (h : m ∣ n) :
    ((1 : rootsOfUnity n R) : Units R) ^ (n / m) =
      ((1 : rootsOfUnity m R) : Units R) := sorry

/-- Raising roots of unity to the quotient exponent preserves multiplication. -/
@[stacks 0BU7 "power map multiplication law for roots of unity"]
theorem powMap_mul (h : m ∣ n) (ζ ξ : rootsOfUnity n R) :
    ((ζ * ξ : rootsOfUnity n R) : Units R) ^ (n / m) =
      ((ζ : Units R) ^ (n / m)) * ((ξ : Units R) ^ (n / m)) := sorry

/-- The canonical homomorphism `μₙ(R) → μₘ(R)` for a divisibility proof `m ∣ n`. -/
@[stacks 0BU7 "power map on roots of unity",
  stacks 09EE "tame inertia roots-of-unity map"]
def powMap (h : m ∣ n) : rootsOfUnity n R →* rootsOfUnity m R where
  toFun ζ := ⟨(ζ : Units R) ^ (n / m), powMap_mem h ζ⟩
  map_one' := Subtype.ext (powMap_one h)
  map_mul' ζ ξ := Subtype.ext (powMap_mul h ζ ξ)

/-- The underlying unit of `powMap` is the expected power. -/
@[simp, stacks 0BU7 "power map application on roots of unity",
  stacks 09EE "tame inertia roots-of-unity map evaluation"]
theorem powMap_coe_apply (h : m ∣ n) (ζ : rootsOfUnity n R) :
    (powMap h ζ : Units R) = (ζ : Units R) ^ (n / m) := sorry

/-- Power maps compose along a chain of divisibility. -/
@[stacks 0BU7 "composition of roots-of-unity power maps"]
theorem powMap_comp (hmn : m ∣ n) (hnk : n ∣ k) :
    (powMap (R := R) (m := m) (n := n) hmn).comp
        (powMap (R := R) (m := n) (n := k) hnk) =
      powMap (R := R) (m := m) (n := k) (hmn.trans hnk) := sorry

end rootsOfUnity
