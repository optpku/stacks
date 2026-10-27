/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.BaseScalarComparison

@[expose] public section

open CategoryTheory

universe uX vX uY vY w

namespace RingedSite.ToposHom

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [Y.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{uX, w}] [UnivLE.{uY, w}]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uY vY, w}]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} X)]
variable [IsGrothendieckAbelian (RingedSite.ModuleCat.{w} Y)]
variable [Fact (∀ a b : Hom.globalSectionsRing X, a * b = b * a)]
variable [Fact (∀ a b : Hom.globalSectionsRing Y, a * b = b * a)]
variable (f : ToposHom X Y)
variable [(SheafOfModules.restrictScalars.{w} f.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived f] [HasModulePushforwardDerived f] [HasModuleDerivedAdjunction f]
variable {R S : Type w} [CommRing R] [CommRing S]
variable (α : R →+* Hom.globalSectionsRing Y) (β : S →+* Hom.globalSectionsRing X)
variable (σ : R →+* S) (h : f.globalSectionsMap.hom.comp α = β.comp σ)

/-- The canonical base-change comparison with ordinary pullback coefficients is the
base scalar comparison followed by derived sections of the left-derived counit. -/
noncomputable def baseScalarComparisonToOrdinary (F : RingedSite.ModuleCat.{w} Y) :=
  let coefficient := (HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} Y)
    (0 : ℤ)).obj F
  let K := (Hom.moduleLocalization.{w} Y).obj coefficient
  let ordinaryPullback := (Functor.totalLeftDerivedCounit
    (modulePullbackToDerived f) (Hom.moduleLocalization.{w} Y)
    (Hom.ModuleQis.{w} Y)).app coefficient
  f.baseScalarComparison α β σ h K ≫
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars β).map
      ((Hom.moduleDerivedGlobalSections.{w} X).map ordinaryPullback)

end RingedSite.ToposHom
