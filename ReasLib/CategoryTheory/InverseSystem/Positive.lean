/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.PNat.Order
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.InverseSystem.Preorder

/-!
# Positive Inverse Systems

This leaf specializes the order-dual inverse-system vocabulary to positive natural numbers.  The
index category is `OrderDual ℕ+`, so a comparison `i ≤ j` supplies a morphism from the stage at
`j` to the stage at `i`.

The generic transition-map API belongs to `OrderDualInverseSystem`; this leaf only adds the
positive-natural successor map and its factorization law.  It is independent of limits, sections,
surjectivity, and additive structure.
-/

@[expose] public section

universe v u

namespace CategoryTheory

/-- A positive sequential inverse system in `C`, indexed by `OrderDual ℕ+`. -/
abbrev PNatInverseSystem (C : Type u) [Category.{v} C] :=
  OrderDualInverseSystem ℕ+ C

namespace PNatInverseSystem

variable {C : Type u} [Category.{v} C]

/-- The object at positive stage `n` of a positive inverse system. -/
abbrev stage (F : PNatInverseSystem C) (n : ℕ+) : C :=
  F.obj (OrderDual.toDual n)

/-- The immediate transition morphism from positive stage `n + 1` to stage `n`. -/
abbrev stepMap (F : PNatInverseSystem C) (n : ℕ+) :
    F.stage (n + 1) ⟶ F.stage n :=
  OrderDualInverseSystem.transitionMap F (PNat.lt_succ_self n).le

/-- The transition from ordinary degree `d + n` back to degree `n`, after converting both
degrees to positive tower indices. -/
@[stacks 0GYM "degree-shifting transition in a positive inverse system"]
abbrev degreeTransition (F : PNatInverseSystem C) (d n : ℕ) :
    F.stage (Nat.succPNat (d + n)) ⟶ F.stage (Nat.succPNat n) :=
  OrderDualInverseSystem.transitionMap F
    (Nat.succPNat_mono (Nat.le_add_left n d))

/-- Degree-shifting transitions commute with the successor maps of a positive inverse system. -/
theorem degreeTransition_step (F : PNatInverseSystem C) (d n : ℕ) :
    F.degreeTransition d (n + 1) ≫ F.stepMap (Nat.succPNat n) =
      F.stepMap (Nat.succPNat (d + n)) ≫ F.degreeTransition d n := sorry

/-- A transition ending at stage `j + 1` factors through the final successor transition. -/
theorem transitionMap_succ_factor (F : PNatInverseSystem C) {i j : ℕ+} (hij : i ≤ j) :
    OrderDualInverseSystem.transitionMap F (hij.trans (PNat.lt_succ_self j).le) =
      F.stepMap j ≫ OrderDualInverseSystem.transitionMap F hij := sorry

end PNatInverseSystem

end CategoryTheory
