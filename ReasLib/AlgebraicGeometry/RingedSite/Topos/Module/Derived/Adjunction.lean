/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

@[expose] public section

open CategoryTheory ComplexShape

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived f] [HasModulePushforwardDerived f]

/-- Absolute-derived pair conditions for the canonical ringed-topos module
adjunction. This is proof-only; the unit and counit are not supplied as data. -/
abbrev HasModuleDerivedAdjunction : Prop :=
  CategoryTheory.Adjunction.TotalDerived.HasPair
    (G := f.modulePullbackHomotopy)
    (F := @Functor.mapHomotopyCategory _ _ _ _ _ _ _ f.modulePushforward
      (modulePushforward_additive f) (up ℤ))
    (RingedSite.Hom.ModuleQis.{w} Y) (RingedSite.Hom.ModuleQis.{w} X)
    (L1 := RingedSite.Hom.moduleLocalization.{w} Y)
    (L2 := RingedSite.Hom.moduleLocalization.{w} X)

/-- The canonical derived pullback--pushforward adjunction, obtained by
deriving the explicit geometric/scalar module adjunction. -/
noncomputable def moduleDerivedAdjunction [HasModuleDerivedAdjunction f] :
    f.modulePullbackDerived ⊣ f.modulePushforwardDerived :=
  CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (G := f.modulePullbackHomotopy)
    (F := @Functor.mapHomotopyCategory _ _ _ _ _ _ _ f.modulePushforward
      (modulePushforward_additive f) (up ℤ))
    (@Adjunction.mapHomotopyCategoryAdjunction _ _ _ _ _ _ _ _
      (modulePullback_additive f) (modulePushforward_additive f) f.moduleAdjunction)
    (RingedSite.Hom.ModuleQis.{w} Y) (RingedSite.Hom.ModuleQis.{w} X)

end RingedSite.ToposHom


namespace RingedSite.ToposHom.NativeDerived

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable (f : ToposHom X Y)
variable [Abelian (ModuleCat.{w} X)] [Abelian (ModuleCat.{w} Y)]
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [HasPullback f] [HasPushforward f]

/-- The absolute-derived pair condition for the native module adjunction. -/
abbrev HasAdjunction : Prop :=
  @CategoryTheory.Adjunction.TotalDerived.HasPair _ _ _ _ _ _ _ _
    f.modulePullbackHomotopy
    (@Functor.mapHomotopyCategory _ _ _ _ _ _ _ f.modulePushforward
      (modulePushforward_additive f) (up ℤ))
    (RingedSite.NativeDerived.quasiIso.{w} Y) (RingedSite.NativeDerived.quasiIso.{w} X)
    (RingedSite.NativeDerived.localization.{w} Y) (RingedSite.NativeDerived.localization.{w} X)
    (RingedSite.NativeDerived.localizationIsLocalization.{w} Y)
    (RingedSite.NativeDerived.localizationIsLocalization.{w} X) inferInstance inferInstance

/-- The adjunction between native unbounded derived inverse and direct image. -/
noncomputable def adjunction [HasAdjunction f] : pullback f ⊣ pushforward f :=
  @CategoryTheory.Adjunction.TotalDerived.HasPair.derived _ _ _ _ _ _ _ _
    f.modulePullbackHomotopy
    (@Functor.mapHomotopyCategory _ _ _ _ _ _ _ f.modulePushforward
      (modulePushforward_additive f) (up ℤ))
    (@Adjunction.mapHomotopyCategoryAdjunction _ _ _ _ _ _ _ _
      (modulePullback_additive f) (modulePushforward_additive f) f.moduleAdjunction)
    (RingedSite.NativeDerived.quasiIso.{w} Y) (RingedSite.NativeDerived.quasiIso.{w} X)
    (RingedSite.NativeDerived.localization.{w} Y) (RingedSite.NativeDerived.localization.{w} X)
    (RingedSite.NativeDerived.localizationIsLocalization.{w} Y)
    (RingedSite.NativeDerived.localizationIsLocalization.{w} X) inferInstance inferInstance inferInstance

end RingedSite.ToposHom.NativeDerived
