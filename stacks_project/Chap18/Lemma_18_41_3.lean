/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.BaseChange.OfSites
import StacksCheckRecall

/-!
# Lemma 18.41.3

Compatibility facade for module base change under the finality criterion.  The four site functors
and their final square remain explicit.  `FinalSquare.ModuleLift` packages exactly the additional
module-linear and structure-ring coherence needed to lift the sheaf-level Beck--Chevalley map; it
does not assume that the resulting module comparison is invertible.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₀ v₀ u₁ v₁ u₂ v₂ u₃ v₃ w z

namespace RingedSite.Hom.FinalSquare

variable {X' : RingedSite.{u₀, v₀, w}} {X : RingedSite.{u₁, v₁, w}}
variable {Y' : RingedSite.{u₂, v₂, w}} {Y : RingedSite.{u₃, v₃, w}}
variable (g' : Hom X' X) (f' : Hom X' Y') (f : Hom X Y) (g : Hom Y' Y)
variable [(g'.modulePushforward.{z}).IsRightAdjoint]
variable [(f'.modulePushforward.{z}).IsRightAdjoint]
variable [(f.modulePushforward.{z}).IsRightAdjoint]
variable [(g.modulePushforward.{z}).IsRightAdjoint]

variable (u' : X' ⥤ Y') (v' : X' ⥤ X) (u : X ⥤ Y) (v : Y' ⥤ Y)
variable [u.IsCocontinuous X.siteTopology Y.siteTopology]
variable [u'.IsCocontinuous X'.siteTopology Y'.siteTopology]
variable [v.IsContinuous Y'.siteTopology Y.siteTopology]
variable [v'.IsContinuous X'.siteTopology X.siteTopology]
variable [v.IsCocontinuous Y'.siteTopology Y.siteTopology]
variable [v'.IsCocontinuous X'.siteTopology X.siteTopology]
variable [∀ F : X'ᵒᵖ ⥤ Type z, u'.op.HasPointwiseRightKanExtension F]
variable [∀ F : Xᵒᵖ ⥤ Type z, u.op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify X'.siteTopology (Type z)]
variable [HasWeakSheafify X.siteTopology (Type z)]

variable (sq : CatCommSq v' u' u v)
variable (L : ModuleLift g' f' f g u' v' u v sq)
variable (hfinal : ∀ V : Y',
  (TwoSquare.costructuredArrowRightwards sq.iso.hom V).Final)

/- The sheaf-level finality theorem used by the module-linear lift. -/
#check (CatCommSq.BeckChevalley.comparison_isIso_of_final
  X'.siteTopology X.siteTopology Y'.siteTopology Y.siteTopology sq hfinal :
    IsIso (CatCommSq.BeckChevalley.comparison
      X'.siteTopology X.siteTopology Y'.siteTopology Y.siteTopology sq))

/- Lemma 18.41.3 (0FN3) (1): finality makes the lifted module
direct-image/inverse-image comparison an isomorphism. -/
@[stacks 0FN3 "(1)"]
#check (L.comparison_isIso_of_final hfinal :
  IsIso (L.comparison :
    f.modulePushforward.{z} ⋙ g.modulePullback.{z} ⟶
      g'.modulePullback.{z} ⋙ f'.modulePushforward.{z}))

section LowerShriek

variable [(g'.modulePullback.{z}).IsRightAdjoint]
variable [(g.modulePullback.{z}).IsRightAdjoint]

/- Lemma 18.41.3 (0FN3) (2): the mate gives the corresponding lower-shriek
base-change isomorphism. -/
@[stacks 0FN3 "(2)"]
#check (L.lowerShriekComparison_isIso_of_final hfinal :
  IsIso (L.lowerShriekComparison :
    f'.modulePullback.{z} ⋙ g'.moduleLowerShriek ⟶
      g.moduleLowerShriek ⋙ f.modulePullback.{z}))

end LowerShriek

end RingedSite.Hom.FinalSquare
