/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.7: perfect derived `𝒪_X`-modules form a triangulated object property. -/
@[stacks 08CR "triangulated closure"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_isTriangulated

/- Lemma 20.49.7 (1): the third vertex is perfect when the first two vertices are perfect. -/
@[stacks 08CR "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_obj₃_of_distinguished_triangle

/- Lemma 20.49.7 (2): the second vertex is perfect when the first and third vertices are perfect. -/
@[stacks 08CR "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_obj₂_of_distinguished_triangle

/- Lemma 20.49.7 (3): the first vertex is perfect when the second and third vertices are perfect. -/
@[stacks 08CR "(3)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_obj₁_of_distinguished_triangle
