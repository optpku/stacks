/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Relocalization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.CategoryTheory.Sites.Topos.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# The localization morphism to the ambient ringed topos

For an object `U` of a ringed site, restriction along `@Over.forget X.carrier X.carrier.str U` is the inverse image of
the localization morphism.  This leaf owns the morphism in direct-image form and the canonical
commutative triangle associated to an arrow `V ⟶ U`.

The coefficient universe is independent of both site universes, and the source and target
presentations may have different carrier universes. Thus localization requires no universe-lift
datum in the public API.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace RingedSite.Localization

variable (X : RingedSite.{u, v, w}) (U : X.carrier)
variable [UnivLE.{max u v, w}]

/-- Forgetting ring structure commutes with direct image from the localization at `U` to the
ambient site. -/
noncomputable def toAmbientForgetIso :
    @Functor.sheafPushforwardCocontinuous (X.localization U).carrier X.carrier (X.localization U).carrier.str X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance ⋙
        @sheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w}) inferInstance ≅
      @sheafCompose (X.localization U).carrier (X.localization U).carrier.str RingCat.{w} inferInstance (Type w) inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) (forget RingCat.{w}) inferInstance ⋙
        (@Functor.morphismOfTopoiInOfCocontinuous (X.localization U).carrier (X.localization U).carrier.str X.carrier X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance inferInstance).pushforward :=
  @Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (X.localization U).carrier (X.localization U).carrier.str X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance
    (@Over.forget X.carrier X.carrier.str U) (forget RingCat.{w}) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- The direct-image structure map of the localization morphism, adjoint to the identity of
the restricted structure sheaf. -/
noncomputable def toAmbientStructureMap :
    X.structureSheaf ⟶
      (@Functor.sheafPushforwardCocontinuous (X.localization U).carrier X.carrier (X.localization U).carrier.str X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance).obj (@Sheaf.over X.carrier X.carrier.str X.siteTopology RingCat.{w} inferInstance X.structureSheaf U) :=
  (@Functor.sheafAdjunctionCocontinuous (X.localization U).carrier X.carrier (X.localization U).carrier.str X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance inferInstance).homEquiv _ _
    (𝟙 (@Sheaf.over X.carrier X.carrier.str X.siteTopology RingCat.{w} inferInstance X.structureSheaf U))

/-- The direct-image presentation of ambient localization preserves the canonical internal-ring
operations. -/
theorem toAmbient_isRingCompatible :
    ToposHom.Direct.IsRingCompatible
      (X := X.localization U) (Y := X)
      (@Functor.morphismOfTopoiInOfCocontinuous (X.localization U).carrier (X.localization U).carrier.str X.carrier X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance inferInstance)
      (@Functor.sheafPushforwardCocontinuous (X.localization U).carrier X.carrier (X.localization U).carrier.str X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance)
      (toAmbientForgetIso X U) (toAmbientStructureMap X U) := sorry

/-- The localization morphism from the ringed topos over `U` to its
ambient ringed topos. -/
@[stacks 04IY "ambient localization"]
noncomputable def toAmbient : ToposHom (X.localization U) X :=
  ToposHom.ofDirectImage
    (X := X.localization U) (Y := X)
    (@Functor.morphismOfTopoiInOfCocontinuous (X.localization U).carrier (X.localization U).carrier.str X.carrier X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance inferInstance)
    (@Functor.sheafPushforwardCocontinuous (X.localization U).carrier X.carrier (X.localization U).carrier.str X.carrier.str
        (@Over.forget X.carrier X.carrier.str U) RingCat.{w} inferInstance (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology inferInstance inferInstance)
    (toAmbientForgetIso X U) (toAmbientStructureMap X U)
    (toAmbient_isRingCompatible X U)

section Triangle

variable {U V : X.carrier} (f : @Quiver.Hom X.carrier X.carrier.str.toQuiver V U)
variable [@GrothendieckTopology.HasSheafCompose X.carrier X.carrier.str RingCat.{w} inferInstance (Type w) inferInstance X.siteTopology (forget RingCat.{w})]

/-- The canonical direct-image comparison in the localization triangle. -/
noncomputable def relocalizationTrianglePushforwardIso :
    (ToposHom.comp (relocalization X f) (toAmbient X U)).toTopos.pushforward ≅
      (toAmbient X V).toTopos.pushforward :=
  @Functor.sheafPushforwardCocontinuousComp'
    (X.localization V).carrier (X.localization V).carrier.str
    (X.localization U).carrier (X.localization U).carrier.str X.carrier X.carrier.str
    (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V) (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology U) X.siteTopology
    (@Over.map X.carrier X.carrier.str V U f) (@Over.forget X.carrier X.carrier.str U) inferInstance inferInstance
    (Type w) inferInstance inferInstance inferInstance
    (@Over.forget X.carrier X.carrier.str V) (@Over.mapForget X.carrier X.carrier.str V U f)
    inferInstance inferInstance

/-- Compatibility of the canonical localization-triangle comparison with the ring-valued
direct-image structure maps. -/
theorem relocalizationTriangle_comm :
    (ToposHom.comp (relocalization X f) (toAmbient X U)).directStructureMap ≫
        (@MorphismOfTopoiIn.ringDirectImageNatTrans X.carrier X.carrier.str
          (X.localization V).carrier (X.localization V).carrier.str X.siteTopology
          (@GrothendieckTopology.over X.carrier X.carrier.str X.siteTopology V)
          _ _ inferInstance inferInstance
          (relocalizationTrianglePushforwardIso X f).hom).app
            (X.localization V).structureSheaf =
      (toAmbient X V).directStructureMap := sorry

/-- The relocalization morphism followed by localization to the ambient
ringed topos is canonically `2`-isomorphic to localization at `V`. -/
@[stacks 04IY "commutative triangle"]
noncomputable def relocalizationTriangle :
    ToposHom.TwoIso
      (ToposHom.comp (relocalization X f :
        ToposHom (X.localization V) (X.localization U)) (toAmbient X U))
      (toAmbient X V) where
  homIso := relocalizationTrianglePushforwardIso X f
  comm := relocalizationTriangle_comm X f

end Triangle

-- The morphisms and the direct-image comparison are explicit Kan-extension and adjunction
-- data.  Deferred proof debt is confined to structure-map compatibility.

end RingedSite.Localization
