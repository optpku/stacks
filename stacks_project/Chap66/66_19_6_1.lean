module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Stalk.Spaces
import StacksCheckRecall

open CategoryTheory

universe u

/- 66.19.6.1: The small-étale stalk is canonically identified with the colimit of the right Kan
extension over all étale neighborhoods. For sheaves, this is the corresponding spaces-étale
sheaf. -/
@[stacks 04JZ]
#check (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.isIso_stalkToSpacesColimit :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X : AlgebraicGeometry.AlgebraicSpace S}
    (xbar : AlgebraicGeometry.AlgebraicSpace.GeometricPoint X)
    (F : (AlgebraicGeometry.AlgebraicSpace.smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)),
    CategoryTheory.IsIso
      (AlgebraicGeometry.AlgebraicSpace.GeometricPoint.stalkToSpacesColimit xbar F))
