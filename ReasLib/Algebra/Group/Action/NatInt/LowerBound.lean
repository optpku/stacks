/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Group.Action.NatInt
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Natural translation on lower-bounded integers

Natural-number translation preserves every lower interval in the integers. This file packages
that restriction as a canonical cancellative additive action.
-/

@[expose] public section

namespace AddAction.IntLowerBound

/-- Translating an integer above `k` by a natural number remains above `k`. -/
theorem vadd_mem (k : ℤ) (n : ℕ) (d : {d : ℤ // k ≤ d}) :
    k ≤ (n : ℤ) + (d : ℤ) := by
  exact Int.le_trans d.property (Int.le_add_of_nonneg_left (Int.natCast_nonneg n))

/-- Natural translation restricted to the integers bounded below by `k`. -/
def vadd (k : ℤ) (n : ℕ) (d : {d : ℤ // k ≤ d}) : {d : ℤ // k ≤ d} :=
  ⟨(n : ℤ) + (d : ℤ), vadd_mem k n d⟩

/-- Zero acts trivially under lower-bounded natural translation. -/
theorem zero_vadd_eq (k : ℤ) (d : {d : ℤ // k ≤ d}) :
    vadd k 0 d = d := by
  apply Subtype.ext
  change (0 : ℤ) + (d : ℤ) = (d : ℤ)
  exact zero_add _

/-- Addition of natural translations acts by successive lower-bounded translations. -/
theorem add_vadd_eq (k : ℤ) (m n : ℕ) (d : {d : ℤ // k ≤ d}) :
    vadd k (m + n) d = vadd k m (vadd k n d) := by
  apply Subtype.ext
  change ((m + n : ℕ) : ℤ) + (d : ℤ) = (m : ℤ) + ((n : ℤ) + (d : ℤ))
  rw [Nat.cast_add, add_assoc]

/-- Natural numbers canonically act by translation on the integers bounded below by `k`. -/
@[stacks 01CV "natural translation on lower-bounded integers"]
instance instAddAction (k : ℤ) : AddAction ℕ {d : ℤ // k ≤ d} where
  vadd := vadd k
  zero_vadd := zero_vadd_eq k
  add_vadd := add_vadd_eq k

/-- Coercing a lower-bounded natural translate to `ℤ` gives ordinary addition. -/
@[simp]
theorem coe_vadd (k : ℤ) (n : ℕ) (d : {d : ℤ // k ≤ d}) :
    ((n +ᵥ d : {d : ℤ // k ≤ d}) : ℤ) = (n : ℤ) + (d : ℤ) := rfl

/-- The inclusion of the integers bounded below by `k` into `ℤ` is equivariant for natural
translation. -/
@[stacks 01CV "equivariant inclusion of lower-bounded integers"]
def coeHom (k : ℤ) : {d : ℤ // k ≤ d} →[ℕ] ℤ where
  toFun := Subtype.val
  map_vadd' := coe_vadd k

/-- The equivariant inclusion of lower-bounded integers is the subtype coercion. -/
@[simp]
theorem coeHom_apply (k : ℤ) (d : {d : ℤ // k ≤ d}) :
    coeHom k d = (d : ℤ) := rfl

/-- Natural translation of a lower-bounded integer constructor is the corresponding constructor
over the translated integer. -/
@[simp]
theorem vadd_mk (k : ℤ) (n : ℕ) (d : ℤ) (hd : k ≤ d) :
    n +ᵥ (⟨d, hd⟩ : {d : ℤ // k ≤ d}) =
      (⟨(n : ℤ) + d, vadd_mem k n ⟨d, hd⟩⟩ : {e : ℤ // k ≤ e}) := rfl

/-- Lower-bounded natural translation is cancellative in the point argument. -/
theorem left_cancel (k : ℤ) (n : ℕ) (a b : {d : ℤ // k ≤ d})
    (h : n +ᵥ a = n +ᵥ b) : a = b := by
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  change (n : ℤ) + (a : ℤ) = (n : ℤ) + (b : ℤ) at h'
  exact add_left_cancel h'

/-- Lower-bounded natural translation is cancellative in the scalar argument. -/
theorem right_cancel (k : ℤ) (m n : ℕ) (d : {d : ℤ // k ≤ d})
    (h : m +ᵥ d = n +ᵥ d) : m = n := by
  have h' := congrArg Subtype.val h
  change (m : ℤ) + (d : ℤ) = (n : ℤ) + (d : ℤ) at h'
  exact Int.natCast_inj.mp (add_right_cancel h')

/-- Natural translation on lower-bounded integers is cancellative in both arguments. -/
@[stacks 01CV "cancellative natural translation on lower-bounded integers"]
instance instIsCancelVAdd (k : ℤ) : IsCancelVAdd ℕ {d : ℤ // k ≤ d} where
  left_cancel' := left_cancel k
  right_cancel' := right_cancel k

/-- Translation by a fixed natural number is injective on lower-bounded integers. -/
theorem point_injective (k : ℤ) (n : ℕ) :
    Function.Injective (fun d : {d : ℤ // k ≤ d} ↦ n +ᵥ d) := by
  intro a b h
  exact left_cancel k n a b h

/-- Translation of a fixed lower-bounded integer is injective in the natural scalar. -/
theorem scalar_injective (k : ℤ) (d : {d : ℤ // k ≤ d}) :
    Function.Injective (fun n : ℕ ↦ n +ᵥ d) := by
  intro m n h
  exact right_cancel k m n d h

end AddAction.IntLowerBound
