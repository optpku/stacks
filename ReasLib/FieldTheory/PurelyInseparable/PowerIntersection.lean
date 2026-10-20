/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stable power intersections

The intersection of all positive `p`-power images is the residue-field object used by the Epp and
complete-DVR weak-solution statements.  It is defined independently of a chosen residue-field
presentation so that the same object can be transported across local maps and field extensions.

@stack 09F8
@stack 09F5
@stack 09F9
-/

universe u v

namespace PerfectClosure

/-- The stable `p`-power intersection of a monoid. -/
@[stacks 09F5 "stable positive-power intersection",
  stacks 09F8 "stable positive-power intersection",
  stacks 09F9 "stable positive-power intersection"]
def powerIntersection (R : Type u) [Monoid R] (p : ℕ) : Set R :=
  ⋂ n : ℕ+, Set.range (fun y : R ↦ y ^ (p ^ (n : ℕ)))

/-- Membership in the stable power intersection means having a `p ^ n`-th root for every positive
integer `n`. -/
@[stacks 09F5 "membership in the stable positive-power intersection",
  stacks 09F8 "membership in the stable positive-power intersection",
  stacks 09F9 "membership in the stable positive-power intersection"]
theorem mem_powerIntersection_iff {R : Type u} [Monoid R] {p : ℕ} {x : R} :
    x ∈ powerIntersection R p ↔
      ∀ n : ℕ+, ∃ y : R, y ^ (p ^ (n : ℕ)) = x := sorry

/-- The concrete intersection presentation of `powerIntersection`, useful when connecting to a
source-facing statement that already uses `Set.range`. -/
@[simp, stacks 09F5 "stable positive-power intersection definition",
  stacks 09F8 "stable positive-power intersection definition",
  stacks 09F9 "stable positive-power intersection definition"]
theorem powerIntersection_eq {R : Type u} [Monoid R] (p : ℕ) :
    powerIntersection R p =
      ⋂ n : ℕ+, Set.range (fun y : R ↦ y ^ (p ^ (n : ℕ))) := sorry

/-- A monoid equivalence transports the stable power intersection onto the corresponding
intersection in the target. -/
@[stacks 09F5 "stable power intersection under equivalence",
  stacks 09F8 "stable power intersection under equivalence",
  stacks 09F9 "stable power intersection under equivalence"]
theorem image_powerIntersection {R : Type u} {S : Type v} [Monoid R] [Monoid S]
    (e : R ≃* S) (p : ℕ) :
    e '' powerIntersection R p = powerIntersection S p := sorry

/-- Pulling a stable power intersection back along a monoid equivalence recovers the source
intersection. -/
@[stacks 09F5 "stable power intersection under inverse equivalence",
  stacks 09F8 "stable power intersection under inverse equivalence",
  stacks 09F9 "stable power intersection under inverse equivalence"]
theorem preimage_powerIntersection {R : Type u} {S : Type v} [Monoid R] [Monoid S]
    (e : R ≃* S) (p : ℕ) :
    e ⁻¹' powerIntersection S p = powerIntersection R p := sorry

end PerfectClosure
