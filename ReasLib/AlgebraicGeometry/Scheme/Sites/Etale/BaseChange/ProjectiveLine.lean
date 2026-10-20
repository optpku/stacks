module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProjectiveSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- If torsion étale cohomology commutes with base change for the projection
from the relative projective line over every scheme, then it commutes with
base change for every proper morphism of schemes. -/
theorem cohomologyCommutesWithBaseChange_of_projectiveLine
    (hP1 : ∀ S : Scheme.{u}, CohomologyCommutesWithBaseChange (toBase 1 S))
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    CohomologyCommutesWithBaseChange f := sorry

end AlgebraicGeometry.Scheme.Hom

end

end
