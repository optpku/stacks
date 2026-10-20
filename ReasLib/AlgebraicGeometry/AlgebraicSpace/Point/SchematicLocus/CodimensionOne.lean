module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus

/-!
# Open scheme neighbourhoods of points of local dimension at most one

On a separated locally Noetherian algebraic space, every point of local-ring
dimension at most one lies in an open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every point of local-ring dimension at most one on a separated locally Noetherian
algebraic space has an open neighbourhood which is a scheme. -/
theorem exists_open_isScheme_of_localRingDimAt_le_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelySeparated X] [IsLocallyNoetherian X]
    (x : Points X) (hx : localRingDimAt x ≤ 1) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet :=
  sorry

/-- On a separated locally Noetherian algebraic space, every point of local-ring
dimension at most one lies in the schematic locus. -/
theorem mem_schematicLocus_of_localRingDimAt_le_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelySeparated X] [IsLocallyNoetherian X]
    {x : Points X} (hx : localRingDimAt x ≤ 1) :
    x ∈ (schematicLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
