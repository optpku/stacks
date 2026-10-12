/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

variable (X : RingedSite.{u, v, w}) {U V : X} (f : V ⟶ U)
variable [UnivLE.{max u v, w}]
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The coefficient-forgetful comparison for direct image along relocalization. -/
noncomputable def relocalizationForgetIso :
    (Over.map f).sheafPushforwardCocontinuous RingCat.{w}
          (X.siteTopology.over V) (X.siteTopology.over U) ⋙
        sheafCompose (X.siteTopology.over U) (forget RingCat.{w}) ≅
      sheafCompose (X.siteTopology.over V) (forget RingCat.{w}) ⋙
        (Over.Site.morphismOfTopoi X.siteTopology f).pushforward :=
  Functor.sheafPushforwardCocontinuous.compSheafComposeIso
    (Over.map f) (forget RingCat.{w})
      (X.siteTopology.over V) (X.siteTopology.over U)

/-- The direct-image structure-sheaf map for relocalization. -/
noncomputable def relocalizationStructureMap :
    X.structureSheaf.over U ⟶
      ((Over.map f).sheafPushforwardCocontinuous RingCat.{w}
        (X.siteTopology.over V) (X.siteTopology.over U)).obj
          (X.structureSheaf.over V) :=
  ((Over.map f).sheafAdjunctionCocontinuous RingCat.{w}
      (X.siteTopology.over V) (X.siteTopology.over U)).homEquiv _ _
    ((Functor.sheafPushforwardContinuousComp' (Over.mapForget f)
      RingCat.{w} (X.siteTopology.over V) (X.siteTopology.over U)
        X.siteTopology).app X.structureSheaf).hom

/-- The direct-image presentation of relocalization preserves the canonical internal-ring
operations. -/
theorem relocalization_isRingCompatible :
    ToposHom.Direct.IsRingCompatible
      (X := X.localization V) (Y := X.localization U)
      (Over.Site.morphismOfTopoi X.siteTopology f)
      ((Over.map f).sheafPushforwardCocontinuous RingCat.{w}
        (X.siteTopology.over V) (X.siteTopology.over U))
      (relocalizationForgetIso X f) (relocalizationStructureMap X f) := sorry

/-- Lemma 18.19.5 (04IY): the morphism of ringed topoi induced by relocalization along
`f : V ⟶ U`. -/
@[stacks 04IY "relocalization morphism"]
noncomputable def relocalization : ToposHom (X.localization V) (X.localization U) :=
  ToposHom.ofDirectImage
    (X := X.localization V) (Y := X.localization U)
    (Over.Site.morphismOfTopoi X.siteTopology f)
    ((Over.map f).sheafPushforwardCocontinuous RingCat.{w}
      (X.siteTopology.over V) (X.siteTopology.over U))
    (relocalizationForgetIso X f) (relocalizationStructureMap X f)
    (relocalization_isRingCompatible X f)

-- All direct-image data is built from canonical right Kan extensions and sheaf adjunctions.

end RingedSite.Localization
