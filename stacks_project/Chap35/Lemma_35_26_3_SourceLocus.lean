module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.SourceLocus

open AlgebraicGeometry
open CategoryTheory

universe u

/- The source locus is the supremum of the source opens on which the
restriction of the morphism has the given property. -/
#check (CategoryTheory.MorphismProperty.sourceLocus :
  ∀ (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}},
    (X ⟶ Y) → X.Opens)
