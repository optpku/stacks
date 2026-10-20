/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Monoidal
import StacksCheckRecall

/-!
# Lemma 18.26.2

The tensor comparison for module pullback is owned by
`ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Monoidal`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : X.Hom Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [(PresheafOfModules.pushforward.{z} f.structureSheafMap.hom).IsRightAdjoint]
variable [MonoidalCategory (ModuleCat.{z} Y)] [MonoidalCategory (ModuleCat.{z} X)]
variable [Functor.Monoidal f.modulePullback.{z}]

/- Lemma 18.26.2 (03EL): pullback preserves tensor products functorially. -/
@[stacks 03EL]
#check
  (pullbackTensorNatIso f :
    MonoidalCategory.tensor (ModuleCat.{z} Y) ⋙
        f.modulePullback.{z} ≅
      Functor.prod f.modulePullback.{z} f.modulePullback.{z} ⋙
        MonoidalCategory.tensor (ModuleCat.{z} X))

variable (F G : ModuleCat.{z} Y)

/- The component of the natural isomorphism at `F` and `G`. -/
#check
  (pullbackTensorIso f F G :
    f.modulePullback.{z}.obj (F ⊗ G) ≅
      (f.modulePullback.{z}.obj F ⊗ f.modulePullback.{z}.obj G))

end RingedSite.Hom
