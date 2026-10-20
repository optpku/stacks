module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Injective

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : Scheme.{u}}
variable [∀ W : Scheme.{u}, HasSheafify W.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ W : Scheme.{u},
    HasInjectiveResolutions (Sheaf W.smallEtaleTopology AddCommGrpCat.{u})]

/-- If torsion étale cohomology commutes with base change for proper morphisms
`f : X ⟶ Y` and `g : Y ⟶ Z`, then it commutes with base change for `f ≫ g`. -/
theorem cohomologyCommutesWithBaseChange_comp
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsProper f] [IsProper g]
    (hf : CohomologyCommutesWithBaseChange f)
    (hg : CohomologyCommutesWithBaseChange g) :
    CohomologyCommutesWithBaseChange (f ≫ g) := sorry

end AlgebraicGeometry.Scheme.Hom

end
