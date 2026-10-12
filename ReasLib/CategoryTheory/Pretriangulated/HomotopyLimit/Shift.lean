/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Cone
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Tails of Sequential Homotopy Limits

@stack 08TC

Deleting a finite prefix from a sequential inverse system does not change its
homotopy limit. Comparison data is restricted through the canonical shift of
its source cone, so naturality and all prefix equations remain part of the
cone rather than separate hypotheses.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u v

namespace CategoryTheory.SequentialInverseSystem

variable {D : Type u} [Category.{v} D]

/-- Reindex a family of maps to the stages of an inverse system along its finite tail. The map
at shifted stage `i` is the original map at stage `n + i`. -/
@[stacks 08TC]
abbrev shiftStageMap (K : SequentialInverseSystem D) {X : D}
    (stageMap : ∀ i : ℕ, X ⟶ K.obj (op i)) (n : ℕ) :
    ∀ i : ℕ, X ⟶ (K.shift n).obj (op i) :=
  fun i ↦ stageMap (n + i)

/-- Evaluation of a shifted family of stage maps is evaluation of the original family at the
corresponding tail index. -/
@[simp, stacks 08TC]
theorem shiftStageMap_apply (K : SequentialInverseSystem D) {X : D}
    (stageMap : ∀ i : ℕ, X ⟶ K.obj (op i)) (n i : ℕ) :
    K.shiftStageMap stageMap n i = stageMap (n + i) := sorry

end CategoryTheory.SequentialInverseSystem

namespace CategoryTheory.HomotopyLimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace IsOf

/-- Stacks 08TC: deleting a finite prefix of a sequential inverse system does not change whether
a fixed object is its homotopy limit. -/
@[stacks 08TC]
theorem shift_iff (K : SequentialInverseSystem D) (X : D) (n : ℕ) :
    HomotopyLimit.IsOf K X ↔ HomotopyLimit.IsOf (K.shift n) X := sorry

/-- A homotopy-limit witness for a sequential inverse system gives one for every finite tail. -/
@[stacks 08TC]
theorem shift {K : SequentialInverseSystem D} {X : D}
    (h : HomotopyLimit.IsOf K X) (n : ℕ) :
    HomotopyLimit.IsOf (K.shift n) X := sorry

/-- A homotopy-limit witness for a finite tail extends across the deleted prefix. -/
@[stacks 08TC]
theorem of_shift {K : SequentialInverseSystem D} {X : D} {n : ℕ}
    (h : HomotopyLimit.IsOf (K.shift n) X) : HomotopyLimit.IsOf K X := sorry

end IsOf

namespace Comparison

/-- Stacks 08TC: comparison data restricts nonemptily to every finite tail. Its prescribed map
to shifted stage `i` is the original cone leg at stage `n + i`. -/
@[stacks 08TC]
theorem nonempty_shift {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} (h : Nonempty (Comparison s c)) (n : ℕ) :
    Nonempty (Comparison (s.shift n) c) := sorry

/-- Stacks 08TC: comparison data on a finite tail extends across the deleted prefix. The source
cone already contains the transition compatibility needed for the restored prefix. -/
@[stacks 08TC]
theorem nonempty_of_shift {K : SequentialInverseSystem D} {s : Cone K} {L : D}
    {c : s.pt ⟶ L} {n : ℕ}
    (h : Nonempty (Comparison (s.shift n) c)) :
    Nonempty (Comparison s c) := sorry

end Comparison

end CategoryTheory.HomotopyLimit
