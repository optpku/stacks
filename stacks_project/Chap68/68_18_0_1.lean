module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianSquare
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
variable (p : W ⟶ X) (q : W ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ Y)

/- 68.18.0.1: the displayed square `W -q-> Z` over `X -f-> Y` of algebraic spaces over `S`
is cartesian. -/
@[stacks 0AC1] #check (AlgebraicGeometry.AlgebraicSpace.IsCartesianSquare p q f g : Prop)
