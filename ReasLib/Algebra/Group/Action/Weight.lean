/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Weight pieces for multiplicative group actions

This module defines the locus where an integer power of a fixed group element, acting after one
map, agrees with a second map.
-/

@[expose] public section

universe u v w

namespace MulAction

variable {G : Type u} {M : Type v} {N : Type w}
variable [Group G] [MulAction G N]

/-- The weight-`k` piece is the set where `t ^ k` acting after `mapP` agrees with `mapA`. -/
def weightPiece (t : G) (k : ℤ) (mapP mapA : M → N) : Set M :=
  { ξ | t ^ k • mapP ξ = mapA ξ }

/-- Membership in a weight piece is equivalent to the defining weight equation. -/
@[simp]
theorem mem_weightPiece (t : G) (k : ℤ) (mapP mapA : M → N) (ξ : M) :
    ξ ∈ weightPiece t k mapP mapA ↔ t ^ k • mapP ξ = mapA ξ := sorry

end MulAction
