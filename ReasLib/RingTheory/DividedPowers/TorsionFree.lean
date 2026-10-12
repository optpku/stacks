/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DividedPowers.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Divided powers over torsion-free rings

Over a ring that is torsion-free as a `ℤ`-module, the factorial formula
determines divided powers uniquely. This leaf packages that principle and its
generator criterion independently of any chapter file.
-/

@[expose] public section

universe u

namespace DividedPowers

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- The positive divided-power operations, with codomain restricted to the
distinguished ideal. -/
@[stacks 07GM "positive divided powers"]
abbrev dpowPos (hI : DividedPowers I) (n : ℕ+) : I → I := fun x ↦
  ⟨hI.dpow n x, hI.dpow_mem n.2.ne' x.2⟩

/-- Coercing a positive divided power to the ambient ring recovers `dpow`. -/
@[simp]
theorem coe_dpowPos_apply (hI : DividedPowers I) (n : ℕ+) (x : I) :
    (hI.dpowPos n x : A) = hI.dpow n x := sorry

/-- Lemma 23.2.2 (1) (07GM): the factorial formula for the
ideal-valued positive divided-power operation. -/
@[stacks 07GM "(1)"]
theorem factorial_mul_dpowPos_eq_pow (hI : DividedPowers I) (n : ℕ+) (x : I) :
    ((n : ℕ).factorial : A) * (hI.dpowPos n x : A) = (x : A) ^ (n : ℕ) := sorry

end DividedPowers

namespace Ideal

variable {A : Type u} [CommRing A]

/-- A family of ideal-valued operations satisfies the factorial divided-power
formula. -/
@[stacks 07GM "(3) factorial formula"]
def HasDividedPowerFormula (I : Ideal A) (γ : ℕ+ → I → I) : Prop :=
  ∀ n : ℕ+, ∀ x : I,
    ((n : ℕ).factorial : A) * (γ n x : A) = (x : A) ^ (n : ℕ)

/-- An ideal has generators whose positive powers have the factorial
divisibility required for divided powers. -/
@[stacks 07GM "(4) generator criterion"]
def HasDividedPowerGenerators (I : Ideal A) : Prop :=
  ∃ S : Set A, Ideal.span S = I ∧
    ∀ ⦃x : A⦄, x ∈ S → ∀ ⦃n : ℕ⦄, 1 ≤ n →
      x ^ n ∈ Ideal.span {(n.factorial : A)} • I

/-- Lemma 23.2.2 (2) (07GM): an ideal in a `ℤ`-torsion-free ring has at
most one divided-power structure. -/
@[stacks 07GM "(2)"]
theorem dividedPowersSubsingleton [Module.IsTorsionFree ℤ A] (I : Ideal A) :
    Subsingleton (DividedPowers I) := sorry

/-- The canonical `Subsingleton` instance for divided-power structures over a
`ℤ`-torsion-free ring. -/
instance instSubsingletonDividedPowers [Module.IsTorsionFree ℤ A] (I : Ideal A) :
    Subsingleton (DividedPowers I) := sorry

/-- Any two divided-power structures on an ideal in a `ℤ`-torsion-free
ring coincide. -/
theorem dividedPowers_eq [Module.IsTorsionFree ℤ A]
    {I : Ideal A} (γ δ : DividedPowers I) :
    γ = δ := sorry

/-- Existence of a divided-power structure inducing `γ` is equivalent to
the factorial formula. -/
theorem exists_dividedPowers_iff [Module.IsTorsionFree ℤ A]
    (I : Ideal A) (γ : ℕ+ → I → I) :
    (∃ hI : DividedPowers I, ∀ n : ℕ+, ∀ x : I, hI.dpowPos n x = γ n x) ↔
      I.HasDividedPowerFormula γ := sorry

/-- Lemma 23.2.2 (3) (07GM): the factorial formula characterizes a
unique divided-power structure over a `ℤ`-torsion-free ring. -/
@[stacks 07GM "(3)"]
theorem existsUnique_dividedPowers_iff [Module.IsTorsionFree ℤ A]
    (I : Ideal A) (γ : ℕ+ → I → I) :
    (∃! hI : DividedPowers I, ∀ n : ℕ+, ∀ x : I, hI.dpowPos n x = γ n x) ↔
      I.HasDividedPowerFormula γ := sorry

/-- Lemma 23.2.2 (4) (07GM): an ideal in a `ℤ`-torsion-free ring admits
divided powers exactly when it has factorially divisible generators. -/
@[stacks 07GM "(4)"]
theorem nonempty_dividedPowers_iff [Module.IsTorsionFree ℤ A] (I : Ideal A) :
    Nonempty (DividedPowers I) ↔ I.HasDividedPowerGenerators := sorry

end Ideal
