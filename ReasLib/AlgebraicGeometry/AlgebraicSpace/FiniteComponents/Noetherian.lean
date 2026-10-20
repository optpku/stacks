module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens

/-- A locally Noetherian algebraic space has finitely many irreducible components on
every quasi-compact open of each étale scheme over it. -/
instance instOfIsLocallyNoetherian {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] : HasFiniteIrreducibleComponentsOnCompactOpens X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens
