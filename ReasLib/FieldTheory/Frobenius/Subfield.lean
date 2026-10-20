/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Frobenius subfield

@stack 07P1

This module names the image of Frobenius as a subfield and exposes its elementary membership API.
The construction is useful independently of p-bases, so no p-basis assumptions or notation are
introduced here.
-/

@[expose] public section

universe u

namespace FieldExtension.Frobenius

variable (p : ℕ) (K : Type u) [Field K] [ExpChar K p]

/-- The subfield of `p`-th powers in a field of exponential characteristic `p`. -/
@[stacks 07P1 "p-th power subfield"]
abbrev subfield : Subfield K :=
  (_root_.frobenius K p).fieldRange

/-- The underlying set of the Frobenius subfield is the range of the `p`-th power map. -/
@[stacks 07P1 "underlying set of the p-th power subfield"]
theorem coe_subfield :
    (subfield p K : Set K) = Set.range fun x : K ↦ x ^ p := by
  ext x
  simp [subfield, _root_.frobenius_def]
/- Proof strategy: unfold `subfield`, use `RingHom.coe_fieldRange`, and rewrite
`_root_.frobenius` with `frobenius_def`. -/

/-- Membership in the Frobenius subfield is witnessed by a `p`-th root. -/
@[stacks 07P1 "membership in the p-th power subfield"]
theorem mem_subfield_iff {x : K} :
    x ∈ subfield p K ↔ ∃ y : K, y ^ p = x := by
  simp [subfield, _root_.frobenius_def]
/- Proof strategy: rewrite by `coe_subfield` and unfold membership in `Set.range`. -/

/-- Every `p`-th power belongs to the Frobenius subfield. -/
@[stacks 07P1 "p-th powers belong to the p-th power subfield"]
theorem pow_mem (x : K) :
    x ^ p ∈ subfield p K := by
  simp [subfield, _root_.frobenius_def]
/- Proof strategy: apply `mem_subfield_iff` with witness `x`. -/

end FieldExtension.Frobenius
