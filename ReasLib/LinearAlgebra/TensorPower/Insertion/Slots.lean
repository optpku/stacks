/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.TensorPower.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Inserting distinguished slots in tensor powers

This leaf owns the representation-independent finite-slot operations.  It has
no dependency on symmetric or exterior powers.

@stack 00DP
-/

@[expose] public section

open scoped TensorProduct
open PiTensorProduct

universe u v

namespace TensorPower.Insertion

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- An ordered pair of distinct tensor slots. -/
@[stacks 00DP]
abbrev SlotPair (n : ℕ) := {pq : Fin n × Fin n // pq.1 < pq.2}

/-- The first slot of an ordered pair in degree `n + 2`. -/
abbrev leftSlot {n : ℕ} (p : SlotPair (n + 2)) : Fin (n + 2) := p.1.1

/-- The second slot of an ordered pair in degree `n + 2`. -/
abbrev rightSlot {n : ℕ} (p : SlotPair (n + 2)) : Fin (n + 2) := p.1.2

/-- The first slot, reindexed after deleting the last position. -/
abbrev leftSlotCast {n : ℕ} (p : SlotPair (n + 2)) : Fin (n + 1) :=
  (leftSlot p).castLT (Fin.val_lt_last (Fin.ne_last_of_lt p.2))

/-- An ordered pair can only occur in degree at least two. -/
abbrev two_le {n : ℕ} (p : SlotPair n) : 2 ≤ n :=
  Nat.succ_le_iff.mpr
    (lt_of_le_of_lt (Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt p.2)) p.1.2.isLt)

/-- The canonical equality used to normalize a degree containing two slots. -/
abbrev castEq {n : ℕ} (p : SlotPair n) : n = (n - 2) + 2 :=
  (Nat.sub_add_cancel (two_le p)).symm

/-- Reindex an ordered pair to the normalized degree `(n - 2) + 2`. -/
def castPair {n : ℕ} (p : SlotPair n) : SlotPair (n - 2 + 2) :=
  let e : Fin n ≃ Fin ((n - 2) + 2) := finCongr (castEq p)
  ⟨⟨e p.1.1, e p.1.2⟩, p.2⟩

/-- Insert two entries into an indexed family in slots `p`. -/
abbrev insertAux {n : ℕ} (p : SlotPair (n + 2)) (x y : M) (m : Fin n → M) :
    Fin (n + 2) → M :=
  Fin.insertNth (leftSlot p) x
    (Fin.insertNth ((leftSlotCast p).predAbove (rightSlot p)) y m)

/-- Insert two entries into a pure tensor family in degree `n`. -/
@[stacks 00DP]
def insert (n : ℕ) (p : SlotPair n) (x y : M) (m : Fin (n - 2) → M) : Fin n → M :=
  insertAux (castPair p) x y m ∘ Fin.cast (castEq p)

/-- The inserted family takes the prescribed value in its first distinguished slot. -/
@[simp]
theorem insert_apply_left (n : ℕ) (p : SlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    insert n p x y m p.1.1 = x := sorry

/-- The inserted family takes the prescribed value in its second distinguished slot. -/
@[simp]
theorem insert_apply_right (n : ℕ) (p : SlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    insert n p x y m p.1.2 = y := sorry

/-- Delete the two distinguished slots from a family in normalized degree `n + 2`. -/
abbrev deleteAux {n : ℕ} (p : SlotPair (n + 2)) (v : Fin (n + 2) → M) : Fin n → M :=
  ((leftSlotCast p).predAbove (rightSlot p)).removeNth ((leftSlot p).removeNth v)

/-- Delete the two distinguished slots from a family in degree `n`. -/
@[stacks 00DP "canonical arbitrary-degree two-slot deletion"]
def delete (n : ℕ) (p : SlotPair n) (v : Fin n → M) : Fin (n - 2) → M :=
  deleteAux (castPair p) (v ∘ Fin.cast (castEq p).symm)

/-- Deleting the two entries just inserted recovers the original family. -/
@[simp]
theorem delete_insert (n : ℕ) (p : SlotPair n) (x y : M) (m : Fin (n - 2) → M) :
    delete n p (insert n p x y m) = m := sorry

/-- Deleting and reinserting the selected entries recovers the original family. -/
theorem insert_delete (n : ℕ) (p : SlotPair n) (v : Fin n → M) :
    insert n p (v p.1.1) (v p.1.2) (delete n p v) = v := sorry

/-- The second slot is the `succAbove` image of its normalized index after deleting the first. -/
theorem rightSlot_eq_left_succAbove_predAbove {n : ℕ} (p : SlotPair (n + 2)) :
    rightSlot p = (leftSlot p).succAbove ((leftSlotCast p).predAbove (rightSlot p)) := sorry

/-- The multilinear insertion map in normalized degree. -/
@[stacks 00DP]
noncomputable def twoSlotMultilinearAux (n : ℕ) (p : SlotPair (n + 2)) (x y : M) :
    MultilinearMap R (fun _ : Fin n ↦ M) (⨂[R]^(n + 2) M) :=
  let t : MultilinearMap R (fun _ : Fin (n + 2) ↦ M) (⨂[R]^(n + 2) M) := tprod R
  let q : Fin (n + 1) := (leftSlotCast p).predAbove (rightSlot p)
  (((t.curryMid (leftSlot p)) x).curryMid q) y

/-- The linear insertion map obtained from `twoSlotMultilinearAux` by the tensor universal
property. -/
@[stacks 00DP "canonical normalized linear slot insertion"]
noncomputable def twoSlotMapAux (n : ℕ) (p : SlotPair (n + 2)) (x y : M) :
    ⨂[R]^n M →ₗ[R] ⨂[R]^(n + 2) M :=
  PiTensorProduct.lift (twoSlotMultilinearAux n p x y)

/-- The two-slot insertion map in arbitrary degree. -/
@[stacks 00DP "canonical arbitrary-degree linear slot insertion"]
noncomputable def twoSlotMap (n : ℕ) (p : SlotPair n) (x y : M) :
    ⨂[R]^(n - 2) M →ₗ[R] ⨂[R]^n M :=
  (TensorPower.cast R M (castEq p).symm).toLinearMap.comp
    (twoSlotMapAux (n - 2) (castPair p) x y)

/-- Evaluation of the normalized insertion map on a pure tensor. -/
theorem twoSlotMapAux_tprod {n : ℕ} (p : SlotPair (n + 2)) (x y : M)
    (m : Fin n → M) :
    twoSlotMapAux n p x y (tprod R m) = tprod R (insertAux p x y m) := sorry

/-- Evaluation of the arbitrary-degree insertion map on a pure tensor. -/
theorem twoSlotMap_tprod (n : ℕ) (p : SlotPair n) (x y : M)
    (m : Fin (n - 2) → M) :
    twoSlotMap n p x y (tprod R m) = tprod R (insert n p x y m) := sorry

end

end TensorPower.Insertion
