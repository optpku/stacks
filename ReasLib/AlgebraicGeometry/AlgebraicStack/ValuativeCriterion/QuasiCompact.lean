module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare.ClosedPoint

/-!
# Quasi-compact valuative existence for algebraic stacks

A quasi-compact morphism of algebraic stacks admits a valuative square through
any point in the closure of its image.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a quasi-compact morphism of algebraic stacks, every point in the closure
of its image is the image of the closed point in a valuative square whose
generic arrow comes from the fraction field of its valuation ring. -/
@[stacks 0CL2]
theorem exists_valuativeCommSq_of_mem_closure_range
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiCompact f]
    {y : Points Y}
    (hy : y ∈ closure (Set.range (Points.map f))) :
    ∃ sq : ValuativeCommSq f, sq.closedPointImage = y :=
  sorry

end AlgebraicGeometry.AlgebraicStack
