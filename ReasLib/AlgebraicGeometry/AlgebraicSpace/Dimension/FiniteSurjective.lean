module

public import ReasLib.Topology.Specialization.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Dimension functions after finite surjective descent

If a function on points of an algebraic space pulls back along a surjective
finite morphism to a dimension function, then it is itself a dimension function.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integer-valued function on a decent, locally Noetherian algebraic space is a
dimension function if its pullback along a finite surjective morphism from a
decent, locally Noetherian algebraic space is a dimension function. -/
@[stacks 0ED9]
theorem isDimensionFunction_of_comp_map {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) [Surjective f] [IsFinite f] [IsDecent Y] [IsDecent X]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] {δ : Points X → ℤ}
    (hδ : IsDimensionFunction (δ ∘ Points.map f)) : IsDimensionFunction δ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
