module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideals of elements killed by powers

For a commutative ring `R` and an ideal `I`, `Ideal.powerTorsionIdeal I` is
the ideal of elements whose annihilator contains one power of `I`.  The
definition is deliberately elementwise, so it is convenient for local-ring
arguments while remaining independent of any local-ring hypothesis.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The ideal of elements annihilated by some power of `I`. -/
@[stacks 0BHZ "elements killed by a power of an ideal"]
def powerTorsionIdeal (I : Ideal R) : Ideal R where
  carrier := {x : R | ∃ n : ℕ, I ^ n ≤ Ideal.torsionOf R R x}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simpa [Ideal.torsionOf_zero]
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨max m n, ?_⟩
    intro r hr
    rw [Ideal.mem_torsionOf_iff]
    have hra : r ∈ Ideal.torsionOf R R a :=
      hm <| Ideal.pow_le_pow_right (I := I) (Nat.le_max_left m n) hr
    have hrb : r ∈ Ideal.torsionOf R R b :=
      hn <| Ideal.pow_le_pow_right (I := I) (Nat.le_max_right m n) hr
    rw [Ideal.mem_torsionOf_iff] at hra hrb
    have hra' : r * a = 0 := by simpa [smul_eq_mul] using hra
    have hrb' : r * b = 0 := by simpa [smul_eq_mul] using hrb
    simpa [smul_eq_mul, mul_add, hra', hrb']
  smul_mem' := by
    intro a b hb
    rcases hb with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro r hr
    rw [Ideal.mem_torsionOf_iff]
    have hrb : r ∈ Ideal.torsionOf R R b := hn hr
    rw [Ideal.mem_torsionOf_iff] at hrb
    have hrb' : r * b = 0 := by simpa [smul_eq_mul] using hrb
    calc
      r * (a * b) = a * (r * b) := by ring
      _ = 0 := by simp [hrb']

/-- Membership in `powerTorsionIdeal I` is the uniform annihilation condition for one ideal power.
-/
@[simp, stacks 0BHZ "power-torsion ideal membership"]
theorem mem_powerTorsionIdeal_iff (I : Ideal R) (x : R) :
    x ∈ powerTorsionIdeal I ↔ ∃ n : ℕ, I ^ n ≤ Ideal.torsionOf R R x := sorry

end Ideal
