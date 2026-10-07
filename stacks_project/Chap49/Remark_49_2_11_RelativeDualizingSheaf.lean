module

public import ReasLib.AlgebraicGeometry.Scheme.Module.RelativeDualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Relative dualizing sheaf API compatibility bridge. -/
#check (AlgebraicGeometry.Scheme.Hom.RelativeDualizingSheaf :
  ∀ {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f], Type (u + 1))
