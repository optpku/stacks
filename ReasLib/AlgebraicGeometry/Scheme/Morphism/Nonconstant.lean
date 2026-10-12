/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism is nonconstant when two source points have distinct images. -/
def IsNonconstant {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ x y : X, f x ≠ f y

/-- A scheme morphism is nonconstant if and only if its map on points is not constant. -/
theorem isNonconstant_iff_not_isConstant {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.IsNonconstant ↔ ¬ ∀ x y : X, f x = f y := sorry

end AlgebraicGeometry.Scheme.Hom
