module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
/-! Source facade for the canonical schematic locus. -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.schematicLocus_spec :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (schematicLocusSpace X).functorOfPoints = (schematicLocusSubfunctor X).toFunctor ∧
      schematicLocusι X = (schematicLocusSubfunctor X).ι ∧
      IsOpenImmersion (schematicLocusι X) ∧ IsScheme (schematicLocus X).X ∧
      ∀ x : Points X, x ∈ Set.range (Points.map (schematicLocus X).ι) ↔
        x ∈ schematicLocusPoints X)
