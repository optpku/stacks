/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Squares underlying chosen pullbacks

This module exposes the commutative square determined by explicit chosen
pullback data.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Limits.ChosenPullback

variable {C : Type u} [Category.{v} C]
variable {X Y S : C} {f : X ⟶ S} {g : Y ⟶ S}

/-- The commutative square whose apex and projections are supplied by an
explicit chosen pullback. -/
def square (h : ChosenPullback f g) : Square C where
  f₁₂ := h.p₁
  f₁₃ := h.p₂
  f₂₄ := f
  f₃₄ := g
  fac := h.condition

end CategoryTheory.Limits.ChosenPullback
