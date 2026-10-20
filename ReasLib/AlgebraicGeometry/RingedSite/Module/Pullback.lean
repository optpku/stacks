module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Inverse images of modules on ringed sites

This module gives the module-valued inverse-image functor attached to a morphism
of ringed sites. The structure-level `CommRing/Pullback` leaf gives the commutative inverse-image
structure-sheaf presentation. Both are independent of flatness and of any
particular geometric category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.Hom

/-- The inverse-image functor on module sheaves attached to a morphism of
ringed sites. -/
@[stacks 03D6 "(2)"]
abbrev modulePullback.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] :
    ModuleCat.{z} Y ⥤ ModuleCat.{z} X :=
  @SheafOfModules.pullback.{z} _ _ _ _ Y.siteTopology X.siteTopology f.base
    Y.structureSheaf X.structureSheaf f.base_isContinuous f.structureSheafMap inferInstance

end RingedSite.Hom
