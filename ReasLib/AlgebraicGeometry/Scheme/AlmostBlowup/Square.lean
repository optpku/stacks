/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup

/-!
# Canonical squares for almost blowups

This module constructs the square determined by an almost blowup morphism and
its center, together with its basic computation and pullback properties.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.IsAlmostBlowupSquare

/-- The canonical scheme square attached to an almost blowup morphism and its center. -/
noncomputable def square {X X' : Scheme.{u}} {b : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsAlmostBlowupSquare b I) : Square Scheme.{u} where
  X₁ := (I.comap b).subscheme
  X₂ := X'
  X₃ := I.subscheme
  X₄ := X
  f₁₂ := (I.comap b).subschemeι
  f₁₃ := (I.comapIso b).hom ≫ pullback.snd b I.subschemeι
  f₂₄ := b
  f₃₄ := I.subschemeι
  fac := sorry

/-- The upper-right map of the canonical almost blowup square is the given morphism. -/
@[simp]
theorem square_f₂₄ {X X' : Scheme.{u}} {b : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsAlmostBlowupSquare b I) : h.square.f₂₄ = b := sorry

/-- The lower map of the canonical almost blowup square is the center immersion. -/
@[simp]
theorem square_f₃₄ {X X' : Scheme.{u}} {b : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsAlmostBlowupSquare b I) : h.square.f₃₄ = I.subschemeι := sorry

/-- The canonical square attached to an almost blowup morphism is a pullback square. -/
theorem square_isPullback {X X' : Scheme.{u}} {b : X' ⟶ X} {I : X.IdealSheafData}
    (h : IsAlmostBlowupSquare b I) : h.square.IsPullback := sorry

end AlgebraicGeometry.IsAlmostBlowupSquare
