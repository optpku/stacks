/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import ReasLib.CategoryTheory.Filtration.SequentialInverse

/-!
# Closure principles for sequential inverse filtrations

This file records the generic induction principle behind applications of sequential inverse
filtrations.  Domain-specific notions such as property I remain in their own libraries.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseFiltration

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- An object with a sequential inverse filtration belongs to every isomorphism-closed property
which contains zero and the pieces, and is closed under the successive extensions and the
limiting inverse system. -/
theorem mem_of_closed {admissibleEpi : MorphismProperty C}
    {pieceProperty target : ObjectProperty C} {I : C}
    [target.ContainsZero] [target.IsClosedUnderIsomorphisms]
    (F : SequentialInverseFiltration I admissibleEpi pieceProperty)
    (h_piece : pieceProperty ≤ target)
    (h_extension : ∀ {S : ShortComplex C}, S.ShortExact → admissibleEpi S.g →
      target S.X₁ → target S.X₃ → target S.X₂)
    (h_limit : ∀ (tower : SequentialInverseSystem C) [HasLimit tower],
      (∀ n : ℕ, target (tower.obj (op n))) →
      (∀ n : ℕ, admissibleEpi (tower.transitionMap (Nat.le_succ n))) →
      target (limit tower)) :
    target I := sorry

end CategoryTheory.SequentialInverseFiltration
