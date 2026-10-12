/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.PowerImage
public import ReasLib.RingTheory.RingHom.PowerImage.Surjective

/-!
# Prime-power and scalar-image generation

The predicates in this file are properties of a ring homomorphism, rather than
properties owned by a particular Stacks chapter.  The arithmetic and residue-field
criteria are exposed as small reusable statements so later chapters can import this
leaf directly.

@stack 0BRA
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace PowerGeneration

/-- Elements satisfying the positive prime-power and scalar-image condition for a
ring homomorphism `f`. -/
@[stacks 0BRA "prime-power and scalar-image generators"]
def generators
    (f : R →+* S) (p : ℕ) : Set S :=
  {x : S |
    ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range}

/-- Membership in the prime-power/scalar-image generating set. -/
@[simp, stacks 0BRA "membership in the generating set"]
theorem mem_generators_iff
    (f : R →+* S) (p : ℕ) {x : S} :
    x ∈ generators f p ↔
      ∃ n : ℕ, 0 < n ∧ x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range := sorry

/-- The target is generated as an algebra by elements whose positive `p`-power and
corresponding scalar multiple both lie in the image of `f`. -/
@[stacks 0BRA]
abbrev IsGenerated
    (f : R →+* S) (p : ℕ) : Prop :=
  RingHom.IsGeneratedBy f (generators f p)

/-- A source element is a prime-power/scalar-image generator with exponent `1`. -/
theorem map_mem
    {p : ℕ} (f : R →+* S) (r : R) :
    f r ∈ generators f p := sorry

/-- The prime-power/scalar-image condition is closed under multiplication. -/
theorem mul_mem
    {p : ℕ} (f : R →+* S) {x y : S}
    (hx : x ∈ generators f p) (hy : y ∈ generators f p) :
    x * y ∈ generators f p := sorry

/-- The prime-power/scalar-image condition is closed under addition. -/
theorem add_mem
    {p : ℕ} [Fact p.Prime] (f : R →+* S) {x y : S}
    (hx : x ∈ generators f p) (hy : y ∈ generators f p) :
    x + y ∈ generators f p := sorry

/-- A nonnegative prime-power/scalar-image witness can be normalized to a positive witness. -/
theorem mem_of_nonnegative
    {p : ℕ} (f : R →+* S) {x : S}
    (hx : ∃ n : ℕ, x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range) :
    x ∈ generators f p := sorry

/-- The addition closure remains valid when the two input witnesses are allowed to have
zero exponents; the bridge first normalizes them with `mem_of_nonnegative`. -/
theorem add_mem_of_nonnegative
    {p : ℕ} [Fact p.Prime] (f : R →+* S) {x y : S}
    (hx : ∃ n : ℕ, x ^ (p ^ n) ∈ f.range ∧ p ^ n • x ∈ f.range)
    (hy : ∃ m : ℕ, y ^ (p ^ m) ∈ f.range ∧ p ^ m • y ∈ f.range) :
    x + y ∈ generators f p := sorry

/-- If the prime-power/scalar-image generators adjoin to the whole target, every
target element satisfies the same condition. -/
theorem mem_of_generated
    {p : ℕ} [Fact p.Prime] (f : R →+* S)
    (hgen : IsGenerated f p) :
    ∀ x : S, x ∈ generators f p := sorry

/-- Prime-power/scalar-image generation makes every target element have a positive power in the
source image. -/
theorem isPowerSurjective
    {p : ℕ} [Fact p.Prime] (f : R →+* S)
    (hgen : IsGenerated f p) :
    f.IsPowerSurjective := sorry

end PowerGeneration

end RingHom
