/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Fibered.Inherited.Topos
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.LiftedStructureSheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {τ : StandardTopology}
variable {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
    (StandardTopology.Big.liftedRingedSite τ S)}
variable (f : X ⟶ Y)
variable [HasSheafify (X.p.inheritedTopology (τ.overTopology S)) (Type (u + 1))]
variable [HasSheafify (Y.p.inheritedTopology (τ.overTopology S)) (Type (u + 1))]
variable [∀ P : X.totalᵒᵖ ⥤ Type (u + 1), X.p.op.HasPointwiseRightKanExtension P]
variable [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1), Y.p.op.HasPointwiseRightKanExtension P]
variable [∀ P : X.totalᵒᵖ ⥤ Type (u + 1),
    (toCartesianBasedFunctor f).toFunctor.op.HasPointwiseRightKanExtension P]
variable [(τ.overTopology S).HasSheafCompose (forget RingCat.{u + 1})]
variable [(X.p.inheritedTopology (τ.overTopology S)).HasSheafCompose
    (forget RingCat.{u + 1})]
variable [(Y.p.inheritedTopology (τ.overTopology S)).HasSheafCompose
    (forget RingCat.{u + 1})]
variable [(SheafOfModules.restrictScalars
    (toCartesianBasedFunctor f).inheritedToposHom.structureMap).IsRightAdjoint]

/- 96.7.1.2 (1): a 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over
`(Sch/S)_τ` induces the inverse image `f⁻¹ : Mod(𝒪_Y) ⥤ Mod(𝒪_X)` of the
associated morphism of ringed topoi. Because `f⁻¹ 𝒪_Y ≅ 𝒪_X`, this agrees
with `f^*`. The same functors exist for the Zariski, étale, smooth, syntomic,
and fppf topologies. -/
@[stacks 06WE] #check
  (RingedSite.ToposHom.modulePullback (toCartesianBasedFunctor f).inheritedToposHom :
    RingedSite.ModuleCat.{u + 1} Y.p.inheritedRingedTopos ⥤
      RingedSite.ModuleCat.{u + 1} X.p.inheritedRingedTopos)

/- 96.7.1.2 (2): the matching direct image `f_* : Mod(𝒪_X) ⥤ Mod(𝒪_Y)` of the
associated morphism of ringed topoi. -/
@[stacks 06WE] #check
  (RingedSite.ToposHom.modulePushforward (toCartesianBasedFunctor f).inheritedToposHom :
    RingedSite.ModuleCat.{u + 1} X.p.inheritedRingedTopos ⥤
      RingedSite.ModuleCat.{u + 1} Y.p.inheritedRingedTopos)
