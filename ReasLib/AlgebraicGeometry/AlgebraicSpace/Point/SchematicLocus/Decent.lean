module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

/-!
# Dense schematic locus of decent algebraic spaces

The schematic locus of a decent algebraic space is dense, giving a dense open
subspace that is representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The schematic locus of a decent algebraic space is dense in its space of points. -/
theorem dense_schematicLocus_of_isDecent {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] :
    Dense (schematicLocus X).pointsSet :=
  sorry

/-- Every decent algebraic space has a dense open subspace representable by a scheme. -/
theorem exists_dense_open_isScheme_of_isDecent {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  ⟨schematicLocus X, instIsScheme_schematicLocus X, dense_schematicLocus_of_isDecent X⟩

end AlgebraicGeometry.AlgebraicSpace
