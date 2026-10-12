/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/- 86.4.0.1: over a scheme `S`, the square of algebraic spaces with arrows
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and `g : Y' ⟶ Y` is cartesian,
and `Y'` and `X` are Tor independent over `Y`. -/
@[stacks 0E5B] #check (IsPullback g' f' f g : Prop)

#check (TorIndependentOver (Over.mk f) (Over.mk g) : Prop)
