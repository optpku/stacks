/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Page-Dependent Autoequivalence Shifts

This module provides the page-indexed autoequivalence family obtained from an initial shift and a
fixed derivation shift.  It is independent of any particular source of a spectral sequence, such
as an exact couple.
-/

@[expose] public section

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace ShiftedSpectralSequence

/-- Remark 12.21.5 (Variant) (tag `0AMJ`): the shift on page `r`, obtained by starting with `S`
and postcomposing once with `T` at every derivation step. -/
@[stacks 0AMJ "page shift"]
def pageShift (S T : C ≌ C) (r : ℕ+) : C ≌ C :=
  Nat.rec S (fun _ e ↦ e.trans T) r.natPred

namespace PageShift

/-- The first page carries the initial shift. -/
@[simp, stacks 0AMJ "page shift at one"]
theorem one (S T : C ≌ C) : pageShift S T 1 = S := sorry

/-- The shift on a successor page is obtained by postcomposing the preceding page shift with
`T`. -/
@[simp, stacks 0AMJ "successor page shift"]
theorem succ (S T : C ≌ C) (r : ℕ+) :
    pageShift S T (r + 1) = (pageShift S T r).trans T := sorry

/-- The recursively bracketed page shift is the initial shift followed by the corresponding
nonnegative power of the derivation shift. -/
@[stacks 0AMJ "page shift as a power"]
theorem eq_trans_pow (S T : C ≌ C) (r : ℕ+) :
    pageShift S T r = S.trans (T ^ (r.natPred : ℤ)) := sorry

end PageShift

/-- The zero-based shift family: page zero carries `S`, and each positive page carries one
additional copy of `T` for each page step, starting with `T ∘ S` on page one. -/
@[stacks 0AMK "zero-based page shift"]
def zeroPageShift (S T : C ≌ C) (r : ℕ) : C ≌ C :=
  match r with
  | 0 => S
  | r + 1 => pageShift (S.trans T) T ⟨r + 1, Nat.succ_pos _⟩

namespace ZeroPageShift

/-- The zeroth shift in the zero-based extension is the initial shift. -/
@[simp, stacks 0AMK "zero-based page shift at zero"]
theorem zero (S T : C ≌ C) : zeroPageShift S T 0 = S := sorry

/-- The first positive shift is `T ∘ S`. -/
@[simp, stacks 0AMK "zero-based page shift at one"]
theorem one (S T : C ≌ C) : zeroPageShift S T 1 = S.trans T := sorry

/-- A positive zero-based shift is the positive-page shift starting at `T ∘ S`. -/
@[simp, stacks 0AMK "zero-based page shift at successor"]
theorem succ (S T : C ≌ C) (r : ℕ) :
    zeroPageShift S T (r + 1) = pageShift (S.trans T) T ⟨r + 1, Nat.succ_pos _⟩ := sorry

/-- The shift on zero-based page `r` is `T^r ∘ S`. -/
@[stacks 0AMK "zero-based page shift as a power"]
theorem eq_trans_pow (S T : C ≌ C) (r : ℕ) :
    zeroPageShift S T r = S.trans (T ^ (r : ℤ)) := sorry

end ZeroPageShift

end ShiftedSpectralSequence
end CategoryTheory
