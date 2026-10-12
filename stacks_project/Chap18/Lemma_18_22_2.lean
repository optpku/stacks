/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Morphism
import StacksCheckRecall

/-!
# Lemma 18.22.2

Representable specialization of localization of a ringed-topos morphism.  The coefficient-generic
slice comparison makes the underlying-topos and structure-sheaf specializations share one owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite.Hom

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y) (V : Y)

/- Lemma 18.22.2 (04J7): for ring-valued sheaves, the representable slice square is the same
coefficient-generic direct-image comparison as the localized morphism of ringed sites. -/
@[stacks 04J7 "(ring sheaves)"]
#check (localizationPushforwardIso f V RingCat.{max u v} :
  X.siteTopology.overPullback RingCat.{max u v} (f.base.obj V) ⋙
      f.base.sheafPushforwardOverPost V RingCat.{max u v} ≅
    f.base.sheafPushforwardContinuous RingCat.{max u v}
        Y.siteTopology X.siteTopology ⋙
      Y.siteTopology.overPullback RingCat.{max u v} V)

/- Lemma 18.22.2 (04J7): the ringed component is the canonical restricted structure map of the
site-level localized morphism. -/
@[stacks 04J7 "(structure map)"]
#check localization_structureSheafMap_eq f V

end RingedSite.Hom
