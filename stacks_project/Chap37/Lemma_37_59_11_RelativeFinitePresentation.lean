module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- The relative finite-presentation API is provided by its reusable mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.Modules.finitePresentationOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f], ObjectProperty X.Modules)
