module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.FiberIsoClasses

open CategoryTheory

universe u

/- The Picard projection to schemes over the base. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.toSchemesOver :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X B : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ B), AlgebraicGeometry.AlgebraicSpace.Picard.Obj f ⥤
      AlgebraicGeometry.AlgebraicSpace.CohStack.SchemesOver B)
