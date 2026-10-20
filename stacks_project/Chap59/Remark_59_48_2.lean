/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {X Y : Scheme.{u}} (tau : StandardTopology) (f : X ⟶ Y) [Mono f]

section SheavesOfSets

variable [HasWeakSheafify (tau.overTopology X) (Type (u + 1))]
variable [HasWeakSheafify (tau.overTopology Y) (Type (u + 1))]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type (u + 1),
  (Over.map f).op.HasLeftKanExtension P]
variable (F : Sheaf (tau.overTopology X) (Type (u + 1)))
variable [(Over.map f).op.HasPointwiseLeftKanExtension F.obj]
variable [∀ P : (Over X)ᵒᵖ ⥤ Type (u + 1),
  (Over.map f).op.HasPointwiseRightKanExtension P]

/- Remark 59.48.2 (1): the unit `F ⟶ f_big⁻¹(f_big! F)` is invertible for
sheaves of sets on the big `tau`-site over `X`. -/
@[stacks 04C8]
#check
  (CategoryTheory.Functor.FullyFaithful.sheafAdjunctionContinuous_unit_app_isIso
      (tau.overTopology X) (tau.overTopology Y) (Over.map f)
      (Functor.FullyFaithful.ofFullyFaithful (Over.map f)) F :
    IsIso
      (((Over.map f).sheafAdjunctionContinuous
        (Type (u + 1)) (tau.overTopology X) (tau.overTopology Y)).unit.app F))

end SheavesOfSets

section SheavesOfAbelianGroups

variable [HasWeakSheafify (tau.overTopology X) AddCommGrpCat.{u + 1}]
variable [HasWeakSheafify (tau.overTopology Y) AddCommGrpCat.{u + 1}]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (Over.map f).op.HasLeftKanExtension P]
variable (F : Sheaf (tau.overTopology X) AddCommGrpCat.{u + 1})
variable [(Over.map f).op.HasPointwiseLeftKanExtension F.obj]
variable [∀ P : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
  (Over.map f).op.HasPointwiseRightKanExtension P]

/- Remark 59.48.2 (2): the unit `F ⟶ f_big⁻¹(f_big! F)` is invertible for
sheaves of abelian groups, using the coefficient-specific lower shriek. -/
@[stacks 04C8]
#check
  (CategoryTheory.Functor.FullyFaithful.sheafAdjunctionContinuous_unit_app_isIso
      (tau.overTopology X) (tau.overTopology Y) (Over.map f)
      (Functor.FullyFaithful.ofFullyFaithful (Over.map f)) F :
    IsIso
      (((Over.map f).sheafAdjunctionContinuous
        AddCommGrpCat.{u + 1} (tau.overTopology X) (tau.overTopology Y)).unit.app F))

end SheavesOfAbelianGroups
