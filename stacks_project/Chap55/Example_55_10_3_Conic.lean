module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.SplitConic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- The split-conic structure morphism over its coefficient ring. -/
#check (AlgebraicGeometry.SplitConic.toSpec :
  ∀ (R : Type u) [CommRing R] (π : R),
    AlgebraicGeometry.SplitConic.model R π ⟶ Spec (CommRingCat.of R))
