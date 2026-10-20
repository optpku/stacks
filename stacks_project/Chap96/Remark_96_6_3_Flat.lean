/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Flat

@[expose] public section
open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory
universe u
variable {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
variable [HasSmallAssociatedTypeSections f τ]

#check (AlgebraicGeometry.GroupoidsOver.associatedRingedToposHom_restrictScalars_isRightAdjoint f τ :
  (SheafOfModules.restrictScalars.{u} (associatedRingedToposHom f τ).structureMap).IsRightAdjoint)

#check (AlgebraicGeometry.GroupoidsOver.associatedRingedToposHom_isFlat_spec f τ :
  @RingedSite.ToposHom.IsFlat.{u + 1, u, u + 1, u, u}
      _ _ inferInstance inferInstance (associatedRingedToposHom f τ)
      (associatedRingedToposHom_restrictScalars_isRightAdjoint f τ) ∧
    IsIso (associatedRingedToposHom f τ).structureMap)
