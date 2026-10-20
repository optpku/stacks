/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct images of modules on ringed sites

This module gives the module-valued direct-image functor attached to a morphism
of ringed sites. It is independent of the geometry used to construct the sites.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.Hom

/-- The direct-image functor on module sheaves attached to a morphism of
ringed sites. -/
@[stacks 03D6 "(1)"]
abbrev modulePushforward.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y) :
    ModuleCat.{z} X ⥤ ModuleCat.{z} Y :=
  @SheafOfModules.pushforward.{z} _ _ _ _ Y.siteTopology X.siteTopology f.base
    Y.structureSheaf X.structureSheaf f.base_isContinuous f.structureSheafMap

end RingedSite.Hom
