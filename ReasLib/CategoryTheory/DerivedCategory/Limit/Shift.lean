/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Shift

@[expose] public section

/-!
# Finite Shifts of Sequential Derived Limits

Deleting a finite prefix from a sequential inverse system does not change its
derived limit.  The category-neutral invariance and reindexing API is owned by
`HomotopyLimit.Shift`; this file retains the historical `IsDerivedLimit`
statements as a compatibility facade.
-/

open CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]

namespace IsDerivedLimit

/-- Stacks 08TC: deleting any finite prefix of a sequential inverse system
does not change whether a fixed object admits a derived-limit presentation. -/
@[stacks 08TC]
theorem nonempty_shift_iff (Ksys : SequentialInverseSystem D) (K : D)
    (n : ℕ) :
    Nonempty (IsDerivedLimit Ksys K) ↔
      Nonempty (IsDerivedLimit (Ksys.shift n) K) := sorry

/-- A derived-limit presentation exists for every finite shift whenever one
exists for the original sequential inverse system. -/
@[stacks 08TC]
theorem nonempty_shift {Ksys : SequentialInverseSystem D} {K : D}
    (h : Nonempty (IsDerivedLimit Ksys K)) (n : ℕ) :
    Nonempty (IsDerivedLimit (Ksys.shift n) K) := sorry

/-- A derived-limit presentation for a finite shift yields one for the
original sequential inverse system. -/
@[stacks 08TC]
theorem nonempty_of_shift {Ksys : SequentialInverseSystem D} {K : D}
    {n : ℕ} (h : Nonempty (IsDerivedLimit (Ksys.shift n) K)) :
    Nonempty (IsDerivedLimit Ksys K) := sorry

namespace Comparison

/-- Stacks 08TC: compatible comparison data restricts to every finite tail;
the prescribed map to shifted stage `i` is the original map to stage `n + i`.
Only existence is exposed, so no proof-dependent comparison data is selected. -/
@[stacks 08TC]
theorem nonempty_shift {Ksys : SequentialInverseSystem D} {X L : D}
    {c : X ⟶ L} {stageMap : ∀ i : ℕ, X ⟶ Ksys.obj (op i)}
    (h : Nonempty (Comparison Ksys c stageMap)) (n : ℕ) :
    Nonempty
      (Comparison (Ksys.shift n) c (Ksys.shiftStageMap stageMap n)) := sorry

/-- Stacks 08TC: compatible comparison data on a finite tail extends across
the deleted prefix when every prescribed prefix map factors from stage `n`
through the corresponding transition map. -/
@[stacks 08TC]
theorem nonempty_of_shift {Ksys : SequentialInverseSystem D} {X L : D}
    {c : X ⟶ L} {stageMap : ∀ i : ℕ, X ⟶ Ksys.obj (op i)} {n : ℕ}
    (h : Nonempty
      (Comparison (Ksys.shift n) c (Ksys.shiftStageMap stageMap n)))
    (h_prefix : ∀ i : ℕ, ∀ hi : i ≤ n,
      stageMap n ≫ Ksys.transitionMap hi = stageMap i) :
    Nonempty (Comparison Ksys c stageMap) := sorry

end Comparison

end IsDerivedLimit

end

end CategoryTheory
