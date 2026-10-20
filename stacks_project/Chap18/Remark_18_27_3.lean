/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.InternalHom
import StacksCheckRecall

/-!
# Remark 18.27.3 compatibility entry point

The pullback--internal-Hom comparison and its naturality API are owned by
`ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.InternalHom`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe uX vX uY vY w z

namespace RingedSite.Hom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y) [f.modulePushforward.{z}.IsRightAdjoint]
variable [MonoidalCategory (ModuleCat.{z} Y)] [MonoidalClosed (ModuleCat.{z} Y)]
variable [MonoidalCategory (ModuleCat.{z} X)] [MonoidalClosed (ModuleCat.{z} X)]
variable [f.modulePullback.{z}.LaxMonoidal]
variable (F G : ModuleCat.{z} Y)

/- Remark 18.27.3: pullback of an internal Hom maps canonically to the internal Hom of the
pullbacks. -/
@[stacks 0GMX]
#check (pullbackInternalHomComparison f F G :
  f.modulePullback.{z}.obj ((ihom F).obj G) ⟶
    (ihom (f.modulePullback.{z}.obj F)).obj (f.modulePullback.{z}.obj G))

/- The reusable owner also packages these components as a natural transformation in `G`. -/
#check (PullbackInternalHom.natTrans f F :
  ihom F ⋙ f.modulePullback.{z} ⟶
    f.modulePullback.{z} ⋙ ihom (f.modulePullback.{z}.obj F))

end RingedSite.Hom
