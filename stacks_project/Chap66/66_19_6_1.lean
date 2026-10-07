module

public import stacks_project.Chap66.«66_19_6_1_Neighborhood»
public import stacks_project.Chap66.«66_19_6_1_Stalk»

/-!
# Identification of the small-étale stalk with the colimit over all étale neighborhoods
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- 66.19.6.1: `stalk xbar F` is identified with
`spacesEtaleStalk xbar (correspondingSpacesPresheaf F)`, i.e. the stalk `F_xbar` of a
presheaf `F` on `smallEtaleSite X` equals the colimit of `F'(U)` over all étale neighborhoods
`(U, ubar)` of `xbar`, where `F'` is the sheaf on `spacesEtaleSite X` corresponding to `F`. -/
@[stacks 04JZ]
theorem isIso_stalkToSpacesColimit (xbar : GeometricPoint X)
    (F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1)) :
    IsIso (stalkToSpacesColimit xbar F) := sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
