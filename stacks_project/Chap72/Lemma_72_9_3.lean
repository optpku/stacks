module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.CodimensionOne
import StacksCheckRecall

/-!
# Open scheme neighbourhoods of points of local dimension at most one

On a separated locally Noetherian algebraic space, every point of local-ring
dimension at most one lies in an open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.9.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x` be a point of `X`. If `X` is separated and locally Noetherian, and the
dimension of the local ring of `X` at `x` is at most `1`, then there exists an
open subspace of `X` containing `x` which is a scheme. -/
@[stacks 0ADD] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_open_isScheme_of_localRingDimAt_le_one :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelySeparated X]
      [IsLocallyNoetherian X] (x : Points X),
      localRingDimAt x ≤ 1 →
        ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet)

/- On a separated locally Noetherian algebraic space, every point of local-ring
dimension at most one lies in the schematic locus. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.mem_schematicLocus_of_localRingDimAt_le_one :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsAbsolutelySeparated X]
      [IsLocallyNoetherian X] {x : Points X},
      localRingDimAt x ≤ 1 → x ∈ (schematicLocus X).pointsSet)
