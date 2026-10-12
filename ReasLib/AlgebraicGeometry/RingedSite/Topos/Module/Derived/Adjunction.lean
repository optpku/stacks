/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
