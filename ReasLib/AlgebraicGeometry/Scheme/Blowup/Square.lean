/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The canonical square of a blowup, with its center and inverse-image exceptional subscheme. -/
noncomputable def square {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [LocallyOfFinitePresentation I.subschemeι] [AlgebraicGeometry.IsBlowup b I] :
    CategoryTheory.Square Scheme.{u} where
  X₁ := (I.comap b).subscheme
  X₂ := X'
  X₃ := I.subscheme
  X₄ := X
  f₁₂ := (I.comap b).subschemeι
  f₁₃ := (I.comapIso b).hom ≫ pullback.snd b I.subschemeι
  f₂₄ := b
  f₃₄ := I.subschemeι
  fac := sorry

/-- The canonical square of a blowup is a pullback square. -/
theorem square_isPullback {X X' : Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [LocallyOfFinitePresentation I.subschemeι] [AlgebraicGeometry.IsBlowup b I] :
    (square I b).IsPullback := sorry

end AlgebraicGeometry.IsBlowup
