/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Multiplicative Submonoid `1 + I`

This leaf defines the multiplicative submonoid formed by the elements that
are congruent to `1` modulo a two-sided ideal.

@stack 04PS
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Semiring R]

/-- Products of elements represented as `1 + I` remain represented as `1 + I`. -/
theorem oneAdd_mul_mem {I : Ideal R} [I.IsTwoSided] {a b : R}
    (ha : ∃ x ∈ I, a = 1 + x) (hb : ∃ y ∈ I, b = 1 + y) :
    ∃ z ∈ I, a * b = 1 + z := sorry

/-- The multiplicative submonoid `1 + I` associated to a two-sided ideal `I`. -/
@[stacks 04PS "multiplicative submonoid 1 + I"]
def oneAdd (I : Ideal R) [I.IsTwoSided] : Submonoid R where
  carrier := {x : R | ∃ y ∈ I, x = 1 + y}
  one_mem' := ⟨0, I.zero_mem, (add_zero 1).symm⟩
  mul_mem' := fun ha hb ↦ oneAdd_mul_mem ha hb

/-- Membership in `I.oneAdd` means being representable as `1 + y` for some `y ∈ I`. -/
@[simp]
theorem mem_oneAdd_iff {I : Ideal R} [I.IsTwoSided] {x : R} :
    x ∈ I.oneAdd ↔ ∃ y ∈ I, x = 1 + y := sorry

/-- An element of `I` gives the corresponding element of the submonoid `1 + I`. -/
@[stacks 04PS "constructor for the multiplicative submonoid 1 + I"]
theorem one_add_mem_oneAdd {I : Ideal R} [I.IsTwoSided] {x : R} (hx : x ∈ I) :
    1 + x ∈ I.oneAdd := sorry

end Ideal
