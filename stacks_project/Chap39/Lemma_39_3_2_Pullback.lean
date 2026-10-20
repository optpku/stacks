module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Pullback

@[expose] public section

open CategoryTheory

universe u

/- The pullback construction remains available to modules importing this compatibility module. -/
#check (@AlgebraicGeometry.Scheme.PreRelation.pullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {U U' : Over S},
    AlgebraicGeometry.Scheme.PreRelation U → (U' ⟶ U) →
      AlgebraicGeometry.Scheme.PreRelation U')
