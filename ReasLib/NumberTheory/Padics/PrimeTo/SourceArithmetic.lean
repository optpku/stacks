/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Padics.PrimeTo.Basic
import Mathlib.Tactic

@[expose] public section

universe u

namespace PadicInt.PrimeTo.SourceArithmetic

open PadicInt

/-- All prime-to-q reductions jointly distinguish elements of the actual
product of adic integer rings. -/
theorem ext_of_reductions (q : ℕ) (x y : PrimeTo q)
    (h : ∀ (m : ℕ) [NeZero m] (hm : m.Coprime q),
      PrimeTo.toZMod q m hm x = PrimeTo.toZMod q m hm y) : x = y := by
  funext p
  -- Local instance justification (proof-local temporary data): the selected
  -- product index supplies its own actual prime-number proof.
  -- Local instance justification (proof-local temporary data): This chosen product index supplies the actual prime proof for its p-adic component.
  letI : Fact p.1.val.Prime := ⟨p.1.property⟩
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  cases k with
  | zero =>
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
  | succ k =>
      let m := p.1.val ^ (k + 1)
      -- Local instance justification (proof-local temporary data): the
      -- reduction modulus is a positive prime power chosen in this proof.
      -- Local instance justification (proof-local temporary data): The reduction modulus is this positive power of the selected prime.
      letI : NeZero m := ⟨pow_ne_zero _ p.1.property.ne_zero⟩
      have hc : m.Coprime q :=
        (p.1.property.coprime_iff_not_dvd.mpr p.2).pow_left _
      have hpdiv : p.1.val ∣ m := ⟨p.1.val ^ k, by simp [m, pow_succ, mul_comm]⟩
      let r : m.primeFactors := ⟨p.1.val, p.1.property.mem_primeFactors' hpdiv⟩
      have heq := congrArg (fun z => ZMod.equivPi m (NeZero.ne m) z r) (h m hc)
      rw [PrimeTo.toZMod_comp_eval, PrimeTo.toZMod_comp_eval] at heq
      change PadicInt.toZModPow (m.factorization p.1.val) (x p) =
        PadicInt.toZModPow (m.factorization p.1.val) (y p) at heq
      have hf : m.factorization p.1.val = k + 1 := Nat.factorization_pow_self p.1.property
      rw [hf] at heq
      exact heq

/-- The degree-one congruences identify the product of the distinguished integer and unit
with that integer minus the degree-one cardinality. -/
theorem integral_value_of_first_count (q : ℕ) (u : (PrimeTo q)ˣ)
    (S : ℕ → Type u) [∀ d, Finite (S d)]
    (h : ∀ (m : ℕ) [NeZero m] (hm : m.Coprime q),
      PrimeTo.trivialModuleCongruence q 1 m hm u S) :
    (q : PrimeTo q) * u.val = ((q : ℤ) - Nat.card (S 1) : ℤ) := by
  apply ext_of_reductions
  intro m _ hm
  have hfirst := h m hm
  simp [PrimeTo.trivialModuleCongruence] at hfirst
  simp only [Int.cast_sub, Int.cast_natCast, map_sub, map_mul, map_natCast]
  linear_combination -hfirst

end PadicInt.PrimeTo.SourceArithmetic

namespace PadicInt.PrimeTo

/-- Extend a positive-degree family by the empty family in degree zero. -/
def natFamily (ι : ℕ+ → Type u) : ℕ → Type u
  | 0 => PEmpty
  | n + 1 => ι ⟨n + 1, Nat.succ_pos n⟩

/-- Extending finite positive-degree families by an empty zero degree preserves finiteness. -/
instance natFamily_finite (ι : ℕ+ → Type u) [∀ d, Finite (ι d)] (n : ℕ) :
    Finite (natFamily ι n) := by
  cases n <;> dsimp [natFamily] <;> infer_instance

/-- The extension of a positive-degree family agrees with that family in degree one. -/
@[simp] theorem natFamily_one (ι : ℕ+ → Type u) : natFamily ι 1 = ι 1 := rfl

/-- Reduction modulo every positive modulus coprime to a positive integer separates integers. -/
theorem int_eq_of_primeTo_reductions (q : ℕ) (hq : 1 ≤ q) (x y : ℤ)
    (h : ∀ (m : ℕ) [NeZero m], m.Coprime q → (x : ZMod m) = (y : ZMod m)) : x = y := by
  sorry

/-- Zero weighted counts in every positive degree mean all positive-degree families are empty. -/
theorem all_empty_of_zero_counts (ι : ℕ+ → Type u) [∀ d, Finite (ι d)]
    (h : ∀ n : ℕ, 0 < n → ∑ d ∈ n.divisors, d * Nat.card (natFamily ι d) = 0) :
    ∀ d : ℕ+, IsEmpty (ι d) := by
  sorry

end PadicInt.PrimeTo
