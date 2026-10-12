/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

open CategoryTheory

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (d : ℕ)

/- Definition 29.34.13: a scheme morphism `f : X ⟶ S` is smooth of relative dimension `d` when
it is smooth and its relative differential sheaf `Ω[f.toShHom]` is finite locally free of
constant rank `d`. -/
@[stacks 02G2] #check (AlgebraicGeometry.SmoothOfRelativeDimension d f : Prop)

/- The canonical relative-dimension property includes smoothness of the morphism. -/
#check (AlgebraicGeometry.SmoothOfRelativeDimension.smooth :
  ∀ (d : ℕ) {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [AlgebraicGeometry.SmoothOfRelativeDimension d f], AlgebraicGeometry.Smooth f)
