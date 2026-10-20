module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Category

universe u

#check (AlgebraicGeometry.AlgebraicSpace.CoherentFormalModules :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S)
    (I : AlgebraicGeometry.AlgebraicSpace.IdealSubobject X), Type (u + 1))
