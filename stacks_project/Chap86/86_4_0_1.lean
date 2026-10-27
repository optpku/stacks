/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.TorIndependence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/- 86.4.0.1: over a scheme `S`, the square of algebraic spaces with arrows
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and `g : Y' ⟶ Y` is cartesian,
and `Y'` and `X` are Tor independent over `Y`. -/
@[stacks 0E5B] #check (CategoryTheory.IsPullback g' f' f g : Prop)

#check (AlgebraicGeometry.AlgebraicSpace.TorIndependentOver (Over.mk f) (Over.mk g) : Prop)
