/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived module pushforward along a morphism of ringed topoi

This file derives the presentation-independent module direct image attached to
`RingedSite.ToposHom`.  It is the right-derived counterpart of the sibling pullback owner and
does not replace the underlying morphism of topoi by a chosen morphism of sites.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]

/-- The homotopy-to-derived functor induced by module direct image along an arbitrary morphism of
site-presented ringed topoi. -/
@[stacks 08J6 "ringed-topos pushforward to the derived category"]
abbrev modulePushforwardToDerived (f : ToposHom X Y)
    [UnivLE.{max uY vY, w}] :
    RingedSite.Hom.ModuleHomotopy.{w} X ⥤ RingedSite.Hom.ModuleDerived.{w} Y :=
  @Functor.mapHomotopyCategory _ _ _ _ _ _ _ f.modulePushforward
      (RingedSite.ToposHom.modulePushforward_additive f) (up ℤ) ⋙
    RingedSite.Hom.moduleLocalization Y

/-- Existence of the unbounded total right-derived module direct image along a morphism of
ringed topoi. -/
@[stacks 08J6 "existence of ringed-topos derived pushforward"]
abbrev HasModulePushforwardDerived (f : ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}] : Prop :=
  Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
    (RingedSite.Hom.ModuleQis.{w} X)

/-- A Grothendieck-abelian source supplies the canonical total right-derived module direct image. -/
@[stacks 08J6 "existence from the Grothendieck module category"]
theorem modulePushforwardToDerived.hasRightDerived
    (f : ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)] :
    Functor.HasRightDerivedFunctor (modulePushforwardToDerived f)
      (RingedSite.Hom.ModuleQis.{w} X) :=
  @Functor.RightDerived.KInjective.hasDerived
    (RingedSite.ModuleCat.{w} X) inferInstance inferInstance
    (RingedSite.ModuleCat.{w} Y) inferInstance inferInstance
    (RingedSite.Hom.moduleCat_hasDerivedCategory.{w} Y)
    f.modulePushforward (modulePushforward_additive f) inferInstance

/-- The canonical unbounded total right-derived direct image on modules along an arbitrary
morphism of site-presented ringed topoi. -/
@[stacks 08J6 "ringed-topos derived module pushforward"]
noncomputable abbrev modulePushforwardDerived (f : ToposHom X Y)
    [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
    [HasModulePushforwardDerived f] :
    RingedSite.Hom.ModuleDerived.{w} X ⥤ RingedSite.Hom.ModuleDerived.{w} Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (RingedSite.Hom.moduleLocalization X) (RingedSite.Hom.ModuleQis X)

end RingedSite.ToposHom
