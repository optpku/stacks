/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Localization
import StacksCheckRecall

/-!
# Lemma 18.22.1

Compatibility facade for localization of a site-presented ringed-topos morphism at an arbitrary
sheaf.  The slice construction is owned generically by `LeftExactAdjunction.localization`; the
forgotten structure-sheaf map is owned by the ringed specialization in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe uX vX uY vY w

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vX, w}]
variable (f : Hom X Y)
variable [PreservesFiniteLimits
  (f.sheafPullback (A := Type w))]
variable (G : Sheaf Y.siteTopology (Type w))

/- Lemma 18.22.1 (04IF): the underlying localized morphism is the canonical localization of
`f⁻¹ ⊣ f_*` at `G`. -/
@[stacks 04IF "(topos morphism)"]
#check (CategoryTheory.LeftExactAdjunction.localization f.toMorphismOfTopoi G :
  LeftExactAdjunction (Over (f.toMorphismOfTopoi.inverseImage.obj G)) (Over G))

/- Lemma 18.22.1 (04IF): its inverse image sends an object over `G` by applying `f⁻¹` to
the structure map. -/
@[stacks 04IF "(inverse image)"]
#check (CategoryTheory.LeftExactAdjunction.localization_inverseImage_obj f.toMorphismOfTopoi G :
  ∀ Z : Over G, (f.toMorphismOfTopoi.localization G).inverseImage.obj Z =
    Over.mk (f.toMorphismOfTopoi.inverseImage.map Z.hom))

/- Lemma 18.22.1 (04IF): localized direct image commutes with the slice-product structure
sheaf. -/
@[stacks 04IF "(direct image)"]
#check (CategoryTheory.LeftExactAdjunction.localization_pushforwardStarIso f.toMorphismOfTopoi G :
  Over.star (f.toMorphismOfTopoi.inverseImage.obj G) ⋙
      (f.toMorphismOfTopoi.localization G).pushforward ≅
    f.toMorphismOfTopoi.pushforward ⋙ Over.star G)

/- Lemma 18.22.1 (04IF): the localized forgotten structure-sheaf map is induced functorially
from `f.underlyingDirectImageMap`. -/
@[stacks 04IF "(structure map)"]
#check (RingedSite.Hom.localizedUnderlyingDirectImageMap f G :
  (Over.star G).obj (underlyingStructureSheaf Y) ⟶
    (f.toMorphismOfTopoi.localization G).pushforward.obj
      ((Over.star (f.toMorphismOfTopoi.inverseImage.obj G)).obj
        (underlyingStructureSheaf X)))

variable (V : Y.carrier)

/- Lemma 18.22.1 (04IF): in the representable case the site-level structure map is the canonical localization formula
from Lemma 18.20.1. -/
@[stacks 04IF "(representable)"]
#check (RingedSite.Hom.localization_structureSheafMap_eq f V :
  (f.localization V).structureSheafMap = RingedSite.Hom.localizationStructureSheafMap f V)

end RingedSite.Hom
