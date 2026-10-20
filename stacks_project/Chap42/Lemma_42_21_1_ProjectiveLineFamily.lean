module

public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveLineFamily

@[expose] public section

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.ProjectiveLineFamily.space :
  {S : Scheme.{u}} → CategoryTheory.Over S → Scheme.{u})

end AlgebraicGeometry
