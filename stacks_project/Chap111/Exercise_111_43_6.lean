module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

section

variable (X : Scheme.{u})

/- Exercise 111.43.6 (1): the rule `U ↦ 𝒪_X(U)ˣ` defines a sheaf of groups
`𝒪_X⁎` on a scheme or locally ringed space. -/
@[stacks 0DAP] #check
  (CategoryTheory.Sheaf.unitsSheaf X.toRingedSpace.sheaf : Sheaf _ CommGrpCat)

#check CategoryTheory.Sheaf.unitsSheaf_obj
#check CategoryTheory.Sheaf.unitsAddSheaf

end

/- Exercise 111.43.6 (2): the Picard group of `X` is identified with
`H¹(X, 𝒪_X⁎)`. -/
@[stacks 0DAP] #check
  (AlgebraicGeometry.Scheme.picardEquivUnitsH1 : ∀ (S : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology S.toRingedSpace) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.toRingedSpace) AddCommGrpCat.{u})],
    S.PicardGroup ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf S.toRingedSpace.sheaf).H 1)

#check @SheafOfModules.RingedSite.PicardGroup.cohomologyEquiv
