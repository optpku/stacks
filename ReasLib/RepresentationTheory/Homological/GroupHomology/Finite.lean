/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

/-!
# Trivial-coefficient homology of finite groups
-/

public section

open CategoryTheory.Limits

universe u

namespace groupHomology

/-- Positive-degree trivial-coefficient homology vanishes when the finite group's order
is invertible in the commutative coefficient ring. -/
theorem isZero_trivial_succ_of_isUnit_card
    {Λ G : Type u} [CommRing Λ] [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Λ)) (n : ℕ) :
    IsZero (groupHomology (Rep.trivial Λ G Λ) (n + 1)) := by
  sorry

end groupHomology
