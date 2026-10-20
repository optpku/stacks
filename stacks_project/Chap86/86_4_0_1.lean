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
@[stacks 0E5B] #check (AlgebraicGeometry.AlgebraicSpace.IsCartesianSquare f' g' g f : Prop)

#check (AlgebraicGeometry.AlgebraicSpace.TorIndependentOver (Over.mk f) (Over.mk g) : Prop)
