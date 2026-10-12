/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zero-Object Bridges

This file records the hypothesis-minimal bridge from simultaneous initial and terminal
structures to the canonical zero-object predicate.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : C}

/-- An object that is both initial and terminal is a zero object; no ambient zero morphisms are
needed for this characterization. -/
@[stacks 0100]
theorem IsInitial.isZero_of_isTerminal (hI : IsInitial X) (hT : IsTerminal X) : IsZero X := sorry

section

variable [HasZeroMorphisms C]

/-- Lemma 12.3.2 (2) [00ZZ]: a morphism factors through a zero object exactly when it is zero. -/
@[stacks 00ZZ]
theorem IsZero.factors_through_iff_eq_zero {X Y Z : C} (hX : IsZero X) (f : Y ⟶ Z) :
    (∃ g : Y ⟶ X, ∃ h : X ⟶ Z, f = g ≫ h) ↔ f = 0 := sorry

end

end CategoryTheory.Limits
