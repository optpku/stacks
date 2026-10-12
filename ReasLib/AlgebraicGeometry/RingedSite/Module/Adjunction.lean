/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback-pushforward adjunction for modules on ringed sites

This file specializes the canonical sheaf-of-modules adjunction to a morphism of ringed sites.
It is the shared owner for the adjunction itself and its Hom equivalence; downstream files should
not rebuild either from the structure-sheaf map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

namespace RingedSite.Hom

/-- Module pullback is left adjoint to module pushforward for a morphism
of ringed sites. -/
@[stacks 03D7]
noncomputable def modulePullbackPushforwardAdjunction.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] :
    f.modulePullback.{z} ⊣ f.modulePushforward.{z} :=
  SheafOfModules.pullbackPushforwardAdjunction.{z} f.structureSheafMap

/-- The Hom equivalence induced by the module pullback-pushforward adjunction. -/
noncomputable def modulePullbackHomEquiv.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y)
    [(f.modulePushforward.{z}).IsRightAdjoint]
    (G : ModuleCat.{z} Y) (F : ModuleCat.{z} X) :
    (f.modulePullback.{z}.obj G ⟶ F) ≃ (G ⟶ f.modulePushforward.{z}.obj F) :=
  (modulePullbackPushforwardAdjunction.{z} f).homEquiv G F

/-- Module pullback is additive; this is inferred from its adjunction to the additive direct-image
functor and should not be supplied as an ambient hypothesis downstream. -/
theorem modulePullback_additive.{z, uX, vX, uY, vY, w}
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : Hom X Y)
    [(f.modulePushforward.{z}).IsRightAdjoint] :
    f.modulePullback.{z}.Additive :=
  SheafOfModules.pullback_additive_of_isRightAdjoint f.structureSheafMap


-- The possible `sorryAx` below is confined to Prop-valued ambient laws supplied by callers; the
-- adjunction and Hom-equivalence data themselves are the canonical mathlib construction.

end RingedSite.Hom
