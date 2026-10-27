/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [HasInjectiveResolutions (ModuleCat.{w} X)]

/-- The degree-`i` higher direct image functor on module sheaves along a morphism
of ringed topoi is the right-derived module pushforward functor. -/
def higherDirectImageModuleFunctor (f : ToposHom X Y) (i : ℕ) :
    ModuleCat.{w} X ⥤ ModuleCat.{w} Y :=
  @Functor.rightDerived _ _ _ _ _ _ _ f.modulePushforward
    (modulePushforward_additive f) i

/-- The degree-`i` higher direct image of a module sheaf along a morphism of
ringed topoi is the value of the higher direct image functor on that sheaf. -/
abbrev higherDirectImageModule (f : ToposHom X Y) (F : ModuleCat.{w} X) (i : ℕ) :
    ModuleCat.{w} Y :=
  (higherDirectImageModuleFunctor f i).obj F

end RingedSite.ToposHom
