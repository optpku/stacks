/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Composition of module pullbacks on ringed sites

This module specializes the sheaf-of-modules pullback composition comparison to morphisms of
ringed sites.  It exposes the comparison in the same direction as composable ringed-site
morphisms, so later derived constructions do not need to rebuild it from structure-sheaf maps.
-/

open CategoryTheory

noncomputable section

namespace RingedSite.Hom

/-- The canonical identification of pullback along `f.comp g` with pullback along `g` followed by
pullback along `f`. This is the standard composition comparison for module pullbacks on ringed
sites.  Its direction matches the standard total-left-derived composition comparison. -/
@[stacks 03D8 "(2)"]
noncomputable abbrev modulePullbackCompIso.{z, uX, vX, uY, vY, uZ, vZ, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    {Z : RingedSite.{uZ, vZ, w}} (f : Hom X Y) (g : Hom Y Z)
    [(f.modulePushforward.{z}).IsRightAdjoint]
    [(g.modulePushforward.{z}).IsRightAdjoint] :
    (Hom.comp f g).modulePullback.{z} ≅
      g.modulePullback.{z} ⋙ f.modulePullback.{z} :=
  (@SheafOfModules.pullbackComp.{z} _ _ _ _ _ _
    Z.siteTopology Y.siteTopology g.base Z.structureSheaf Y.structureSheaf
    g.base_isContinuous g.structureSheafMap inferInstance
    X.siteTopology f.base X.structureSheaf f.base_isContinuous
    (baseComp_isContinuous f g) f.structureSheafMap inferInstance).symm

end RingedSite.Hom

-- The isomorphism data is inherited from the canonical sheaf-of-modules pullback comparison.
