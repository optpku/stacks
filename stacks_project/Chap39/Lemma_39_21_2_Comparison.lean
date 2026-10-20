module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian.ActionEquivalence

universe u

/- Compatibility bridge for consumers of the former comparison module. -/
#check (AlgebraicGeometry.GroupoidScheme.CartesianOver.cartesianActionEquivalence :
  {S : AlgebraicGeometry.Scheme.{u}} →
    (G : AlgebraicGeometry.GroupoidScheme S) →
      AlgebraicGeometry.GroupoidScheme.CartesianOver G ≌
        AlgebraicGeometry.GroupoidScheme.Action G)
