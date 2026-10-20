/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Picard
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

section

variable (X : LocallyRingedSpace.{u})

/- Exercise 111.43.6 (1): the rule `U ↦ 𝒪_X(U)ˣ` defines a sheaf of groups
`𝒪_X⁎` on a scheme or locally ringed space. -/
@[stacks 0DAP] #check
  (CategoryTheory.Sheaf.unitsSheaf X.toRingedSpace.sheaf :
    Sheaf (Opens.grothendieckTopology X.toRingedSpace) CommGrpCat.{u})

#check (CategoryTheory.Sheaf.unitsSheaf_obj X.toRingedSpace.sheaf :
  ∀ (U : (TopologicalSpace.Opens X.toRingedSpace)ᵒᵖ),
    (CategoryTheory.Sheaf.unitsSheaf X.toRingedSpace.sheaf).1.obj U =
      CommGrpCat.of (X.toRingedSpace.sheaf.1.obj U)ˣ)
#check (CategoryTheory.Sheaf.unitsAddSheaf X.toRingedSpace.sheaf :
  Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})

end

/- Exercise 111.43.6 (2): the Picard group of `X` is identified with
`H¹(X, 𝒪_X⁎)`. -/
@[stacks 0DAP] #check
  (AlgebraicGeometry.Scheme.picardEquivUnitsH1 : ∀ (S : Scheme.{u})
    [HasSheafify (Opens.grothendieckTopology S.toRingedSpace) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology S.toRingedSpace) AddCommGrpCat.{u})],
    S.PicardGroup ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf S.toRingedSpace.sheaf).H 1)

section

variable (X : LocallyRingedSpace.{u})
variable [HasExt.{u}
  (Sheaf (Opens.grothendieckTopology X.toRingedSpace) AddCommGrpCat.{u})]

/- Exercise 111.43.6 (3): for a locally ringed space, the Picard group is
identified with `H¹(X, 𝒪_X⁎)`. -/
@[stacks 0DAP] #check
  (SheafOfModules.RingedSite.PicardGroup.cohomologyEquiv X.toRingedSpace.sheaf :
    X.toRingedSpace.PicardGroup ≃+
      (CategoryTheory.Sheaf.unitsAddSheaf X.toRingedSpace.sheaf).H 1)

end
