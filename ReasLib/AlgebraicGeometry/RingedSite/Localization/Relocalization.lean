/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.KanExtension
public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Hom
public import ReasLib.CategoryTheory.Sites.Over.SheafCompose
public import ReasLib.CategoryTheory.Sites.Over.Topos
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.SheafCompose
public import ReasLib.CategoryTheory.Sites.Topos.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relocalization of ringed topoi

An arrow `f : V ⟶ U` in a ringed site induces a morphism from the ringed topos localized at
`V` to the one localized at `U`.  This leaf owns the full morphism data; functor-level
composition comparisons remain in the general site-topos composition layer.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite.Localization

variable (X : RingedSite.{u, v, w}) {U V : X.carrier} (f : @Quiver.Hom X.carrier X.carrier.str.toQuiver V U)
variable [UnivLE.{max u v, w}]
variable [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})]

/-- The coefficient-forgetful comparison for direct image along relocalization. -/
noncomputable def relocalizationForgetIso :
    @Functor.sheafPushforwardCocontinuous (X.localization V).carrier (X.localization U).carrier (X.localization V).carrier.str (X.localization U).carrier.str
        (@Over.map X.carrier X.carrier.str V U f) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) inferInstance inferInstance ⋙
        @sheafCompose (X.localization U).carrier (X.localization U).carrier.str RingCat.{w} inferInstance (Type w) inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) (forget RingCat.{w}) inferInstance ≅
      @sheafCompose (X.localization V).carrier (X.localization V).carrier.str RingCat.{w} inferInstance (Type w) inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (forget RingCat.{w}) inferInstance ⋙
        (@Over.Site.morphismOfTopoi X.carrier X.carrier.str U V X.siteTopology f inferInstance inferInstance inferInstance inferInstance inferInstance).pushforward :=
  @Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (X.localization V).carrier (X.localization V).carrier.str (X.localization U).carrier (X.localization U).carrier.str RingCat.{w} inferInstance (Type w) inferInstance
    (@Over.map X.carrier X.carrier.str V U f) (forget RingCat.{w}) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- The direct-image structure-sheaf map for relocalization. -/
noncomputable def relocalizationStructureMap :
    @Sheaf.over X.carrier X.carrier.str X.siteTopology RingCat.{w} inferInstance X.structureSheaf U ⟶
      (@Functor.sheafPushforwardCocontinuous (X.localization V).carrier (X.localization U).carrier (X.localization V).carrier.str (X.localization U).carrier.str
        (@Over.map X.carrier X.carrier.str V U f) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) inferInstance inferInstance).obj
          (@Sheaf.over X.carrier X.carrier.str X.siteTopology RingCat.{w} inferInstance X.structureSheaf V) :=
  (@Functor.sheafAdjunctionCocontinuous (X.localization V).carrier (X.localization U).carrier (X.localization V).carrier.str (X.localization U).carrier.str
        (@Over.map X.carrier X.carrier.str V U f) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) inferInstance inferInstance inferInstance).homEquiv _ _
    ((@Functor.sheafPushforwardContinuousComp'
      (X.localization V).carrier (X.localization V).carrier.str
      (X.localization U).carrier (X.localization U).carrier.str X.carrier X.carrier.str
      (@Over.map X.carrier X.carrier.str V U f) (@Over.forget X.carrier X.carrier.str U)
      (@Over.forget X.carrier X.carrier.str V) (@Over.mapForget X.carrier X.carrier.str V U f)
      RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U)
        X.siteTopology inferInstance inferInstance inferInstance).app X.structureSheaf).hom

/-- The direct-image presentation of relocalization preserves the canonical internal-ring
operations. -/
theorem relocalization_isRingCompatible :
    ToposHom.Direct.IsRingCompatible
      (X := X.localization V) (Y := X.localization U)
      (@Over.Site.morphismOfTopoi X.carrier X.carrier.str U V X.siteTopology f inferInstance inferInstance inferInstance inferInstance inferInstance)
      (@Functor.sheafPushforwardCocontinuous (X.localization V).carrier (X.localization U).carrier (X.localization V).carrier.str (X.localization U).carrier.str
        (@Over.map X.carrier X.carrier.str V U f) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) inferInstance inferInstance)
      (relocalizationForgetIso X f) (relocalizationStructureMap X f) := sorry

/-- The morphism of ringed topoi induced by relocalization along
`f : V ⟶ U`. -/
@[stacks 04IY "relocalization morphism"]
noncomputable def relocalization : ToposHom (X.localization V) (X.localization U) :=
  ToposHom.ofDirectImage
    (X := X.localization V) (Y := X.localization U)
    (@Over.Site.morphismOfTopoi X.carrier X.carrier.str U V X.siteTopology f inferInstance inferInstance inferInstance inferInstance inferInstance)
    (@Functor.sheafPushforwardCocontinuous (X.localization V).carrier (X.localization U).carrier (X.localization V).carrier.str (X.localization U).carrier.str
        (@Over.map X.carrier X.carrier.str V U f) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) inferInstance inferInstance)
    (relocalizationForgetIso X f) (relocalizationStructureMap X f)
    (relocalization_isRingCompatible X f)

-- All direct-image data is built from canonical right Kan extensions and sheaf adjunctions.

end RingedSite.Localization
