/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ideals of Definition in Local Rings

@stack 00K7
@stack 07DU
@stack 07FE

This module owns the algebraic local-ring meaning of an ideal of definition: its radical is the
maximal ideal.  It is distinct from the topological notion in `TopologicalRing.Ideal`.
-/

universe u

namespace Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- An ideal of a local ring is an ideal of definition when its radical is the maximal ideal. -/
@[stacks 07DU]
def IsIdealOfDefinition (I : Ideal R) : Prop :=
  I.radical = IsLocalRing.maximalIdeal R

/-- In a local ring, an ideal is of definition exactly when its radical is maximal. -/
theorem isIdealOfDefinition_iff_isMaximal_radical {I : Ideal R} :
    I.IsIdealOfDefinition ↔ I.radical.IsMaximal := sorry

namespace IsIdealOfDefinition

/-- The radical of an ideal of definition is maximal. -/
theorem isMaximal_radical {I : Ideal R} (hI : I.IsIdealOfDefinition) :
    I.radical.IsMaximal := sorry

/-- An ideal of definition is primary. -/
theorem isPrimary {I : Ideal R} (hI : I.IsIdealOfDefinition) : I.IsPrimary := sorry

/-- In a Noetherian local ring, two ideals of definition become comparable after
a positive power. -/
@[stacks 00K7 "power comparison for ideals of definition"]
theorem exists_pow_le [IsNoetherianRing R] {I J : Ideal R}
    (hI : I.IsIdealOfDefinition) (hJ : J.IsIdealOfDefinition) :
    ∃ n : ℕ+, J ^ (n : ℕ) ≤ I := sorry

/-- In a Noetherian local ring, every ideal of definition contains a positive
power of the maximal ideal. -/
@[stacks 07FE "positive maximal-ideal power in an ideal of definition"]
theorem exists_maximalIdeal_pow_le [IsNoetherianRing R] {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    ∃ n : ℕ+, IsLocalRing.maximalIdeal R ^ (n : ℕ) ≤ I := sorry

end IsIdealOfDefinition

/-- The maximal ideal of a local ring is an ideal of definition. -/
@[simp]
theorem maximalIdeal_isIdealOfDefinition :
    (IsLocalRing.maximalIdeal R).IsIdealOfDefinition := sorry

end

end Ideal
