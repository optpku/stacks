/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential reindexing of positive inverse systems

The positive index `ℕ+` and the ordinary sequential index `ℕ` differ only by the shift
`n ↦ n + 1`.  This file owns the canonical categorical reindexing, so concrete positive
systems do not need to rebuild an `ofOpSequence` by hand.
@stack 0EGS
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe v u

namespace CategoryTheory.PNatInverseSystem

variable {C : Type u} [Category.{v} C]

/-- The index equivalence from `ℕᵒᵖ` to `OrderDual ℕ+`, induced by `n ↦ n + 1`. -/
@[stacks 0EGS "reindexing positive inverse systems by ordinary sequential indices"]
def indexEquivalence : ℕᵒᵖ ≌ OrderDual ℕ+ :=
  (OrderIso.pnatIsoNat.symm.equivalence.op).trans (orderDualEquivalence ℕ+).symm

/-- Reindex a positive inverse system along the canonical positive-to-sequential equivalence. -/
@[stacks 0EGS "sequential reindexing of a positive inverse system"]
abbrev toSequential (F : PNatInverseSystem C) : SequentialInverseSystem C :=
  indexEquivalence.functor ⋙ F

/-- The sequential object at `n` is the positive object at `n + 1`. -/
@[simp]
theorem toSequential_obj (F : PNatInverseSystem C) (n : ℕ) :
    F.toSequential.obj (op n) = F.stage (Nat.succPNat n) := sorry

/-- The sequential successor map is the positive successor map at `n + 1`. -/
theorem toSequential_stepMap (F : PNatInverseSystem C) (n : ℕ) :
    F.toSequential.stepMap n = F.stepMap (Nat.succPNat n) := sorry

/-- Reindexing a positive inverse system by `n ↦ n + 1` does not change its limit. -/
@[stacks 0EGS "limits are invariant under positive sequential reindexing"]
noncomputable def toSequentialLimitIso (F : PNatInverseSystem C) [HasLimit F] :
    limit F.toSequential ≅ limit F :=
  HasLimit.isoOfEquivalence indexEquivalence (Iso.refl _)

/-- The limit comparison identifies the ordinary `n`th projection with the positive
`(n + 1)`st projection. -/
@[reassoc]
theorem toSequentialLimitIso_hom_comp_π
    (F : PNatInverseSystem C) [HasLimit F] (n : ℕ) :
    F.toSequentialLimitIso.hom ≫ limit.π F (OrderDual.toDual (Nat.succPNat n)) =
      limit.π F.toSequential (op n) := sorry

end CategoryTheory.PNatInverseSystem
