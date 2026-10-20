module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology

/-!
# Closed points of valuative squares of algebraic stacks

The closed point of the valuation-ring spectrum maps to a point of the target
stack along the bottom arrow of a valuative square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace ValuativeCommSq

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}

/-- The closed point of the valuation-ring spectrum in a valuative square. -/
def closedPoint (sq : ValuativeCommSq f) : sq.specR.left :=
  IsLocalRing.closedPoint sq.R

/-- The image in the target stack of the closed point of the valuation-ring spectrum. -/
noncomputable def closedPointImage (sq : ValuativeCommSq f) : Points Y :=
  Points.mapOfSlice sq.i₂ sq.closedPoint

/-- The closed-point image is obtained by applying the bottom arrow's map on points. -/
theorem closedPointImage_spec (sq : ValuativeCommSq f) :
    closedPointImage sq = Points.mapOfSlice sq.i₂ sq.closedPoint :=
  rfl

/-- The closed point of a valuative square is the closed point of its valuation ring. -/
theorem closedPoint_eq (sq : ValuativeCommSq f) :
    closedPoint sq = IsLocalRing.closedPoint sq.R :=
  rfl

end ValuativeCommSq

end AlgebraicGeometry.AlgebraicStack
