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

For an object `U` of a ringed site, restriction along `Over.forget U` is the inverse image of
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

variable (X : RingedSite.{u, v, w}) (U : X)
variable [UnivLE.{max u v, w}]

/-- Forgetting ring structure commutes with direct image from the localization at `U` to the
ambient site. -/
noncomputable def toAmbientForgetIso :
    (Over.forget U).sheafPushforwardCocontinuous RingCat.{w}
          (X.siteTopology.over U) X.siteTopology ⋙
        sheafCompose X.siteTopology (forget RingCat.{w}) ≅
      sheafCompose (X.siteTopology.over U) (forget RingCat.{w}) ⋙
        ((Over.forget U).morphismOfTopoiInOfCocontinuous
          (X.siteTopology.over U) X.siteTopology).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (Over.forget U) (forget RingCat.{w})
      (X.siteTopology.over U) X.siteTopology

/-- The direct-image structure map of the localization morphism, adjoint to the identity of
the restricted structure sheaf. -/
noncomputable def toAmbientStructureMap :
    X.structureSheaf ⟶
      ((Over.forget U).sheafPushforwardCocontinuous RingCat.{w}
        (X.siteTopology.over U) X.siteTopology).obj (X.structureSheaf.over U) :=
  ((Over.forget U).sheafAdjunctionCocontinuous RingCat.{w}
      (X.siteTopology.over U) X.siteTopology).homEquiv _ _
    (𝟙 (X.structureSheaf.over U))

/-- The direct-image presentation of ambient localization preserves the canonical internal-ring
operations. -/
theorem toAmbient_isRingCompatible :
    ToposHom.Direct.IsRingCompatible
      (X := X.localization U) (Y := X)
      ((Over.forget U).morphismOfTopoiInOfCocontinuous
        (X.siteTopology.over U) X.siteTopology)
      ((Over.forget U).sheafPushforwardCocontinuous RingCat.{w}
        (X.siteTopology.over U) X.siteTopology)
      (toAmbientForgetIso X U) (toAmbientStructureMap X U) := sorry

/-- Lemma 18.19.5 (04IY): the localization morphism from the ringed topos over `U` to its
ambient ringed topos. -/
@[stacks 04IY "ambient localization"]
noncomputable def toAmbient : ToposHom (X.localization U) X :=
  ToposHom.ofDirectImage
    (X := X.localization U) (Y := X)
    ((Over.forget U).morphismOfTopoiInOfCocontinuous
      (X.siteTopology.over U) X.siteTopology)
    ((Over.forget U).sheafPushforwardCocontinuous RingCat.{w}
      (X.siteTopology.over U) X.siteTopology)
    (toAmbientForgetIso X U) (toAmbientStructureMap X U)
    (toAmbient_isRingCompatible X U)

section Triangle

variable {U V : X} (f : V ⟶ U)
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The canonical direct-image comparison in the localization triangle. -/
noncomputable def relocalizationTrianglePushforwardIso :
    (ToposHom.comp (relocalization X f) (toAmbient X U)).toTopos.pushforward ≅
      (toAmbient X V).toTopos.pushforward :=
  Functor.sheafPushforwardCocontinuousComp'
    (X.siteTopology.over V) (X.siteTopology.over U) X.siteTopology
    (Over.map f) (Over.forget U) (Over.mapForget f)

/-- Compatibility of the canonical localization-triangle comparison with the ring-valued
direct-image structure maps. -/
theorem relocalizationTriangle_comm :
    (ToposHom.comp (relocalization X f) (toAmbient X U)).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (relocalizationTrianglePushforwardIso X f).hom).app
            (X.localization V).structureSheaf =
      (toAmbient X V).directStructureMap := sorry

/-- Lemma 18.19.5 (04IY): the relocalization morphism followed by localization to the ambient
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
