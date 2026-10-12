/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
  (f.base.sheafPullback (Type w) Y.siteTopology X.siteTopology)]
variable (G : Sheaf Y.siteTopology (Type w))

/- Lemma 18.22.1 (04IF): the underlying localized morphism is the canonical localization of
`f⁻¹ ⊣ f_*` at `G`. -/
@[stacks 04IF "(topos morphism)"]
#check f.toMorphismOfTopoi.localization G

/- Lemma 18.22.1 (04IF): its inverse image sends an object over `G` by applying `f⁻¹` to
the structure map. -/
@[stacks 04IF "(inverse image)"]
#check LeftExactAdjunction.localization_inverseImage_obj f.toMorphismOfTopoi G

/- Lemma 18.22.1 (04IF): localized direct image commutes with the slice-product structure
sheaf. -/
@[stacks 04IF "(direct image)"]
#check f.toMorphismOfTopoi.localization_pushforwardStarIso G

/- Lemma 18.22.1 (04IF): the localized forgotten structure-sheaf map is induced functorially
from `f.underlyingDirectImageMap`. -/
@[stacks 04IF "(structure map)"]
#check f.localizedUnderlyingDirectImageMap G

variable (V : Y)

/- In the representable case the site-level structure map is the canonical localization formula
from Lemma 18.20.1. -/
@[stacks 04IF "(representable)"]
#check localization_structureSheafMap_eq f V

end RingedSite.Hom
