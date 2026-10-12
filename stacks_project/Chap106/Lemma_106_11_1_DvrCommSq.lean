/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import stacks_project.Chap101.«101_39_1_1_ValuativeSquare»
public import stacks_project.Chap101.Definition_101_13_2_Closed

/-!
# Closed points of valuative squares of algebraic stacks

The closed point of `Spec(R)` in a valuative square of algebraic stacks is
compared with `|Y|` along the bottom map of the square.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}

/-- The closed point of `Spec(R)` in a valuative square. -/
def closedPoint (sq : ValuativeCommSq f) : sq.specR.left :=
  IsLocalRing.closedPoint sq.R

/-- The image in `|Y|` of the closed point of `Spec(R)`. -/
noncomputable def closedPointImage (sq : ValuativeCommSq f) : Points Y :=
  Points.mapOfSlice sq.i₂ sq.closedPoint

/-- `closedPointImage` is the image of the closed point of `Spec(R)` along
`sq.i₂`. -/
theorem closedPointImage_spec (sq : ValuativeCommSq f) :
    closedPointImage sq = Points.mapOfSlice sq.i₂ sq.closedPoint :=
  sorry

/-- The closed point of `Spec(R)` is the closed point of the local ring `R`. -/
theorem closedPoint_eq (sq : ValuativeCommSq f) :
    closedPoint sq = IsLocalRing.closedPoint sq.R :=
  sorry

end ValuativeCommSq

end AlgebraicGeometry.AlgebraicStack
