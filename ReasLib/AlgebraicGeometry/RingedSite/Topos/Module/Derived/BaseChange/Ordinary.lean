/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open CategoryTheory

noncomputable section

universe uX vX uX' vX' uS vS uS' vS' w

namespace RingedSite.ToposHom.DerivedBaseChange

variable {X : RingedSite.{uX, vX, w}} {X' : RingedSite.{uX', vX', w}}
  {S : RingedSite.{uS, vS, w}} {S' : RingedSite.{uS', vS', w}}
variable [X.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [X'.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [S.siteTopology.HasSheafCompose (forget RingCat.{w})]
  [S'.siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max uX vX, w}] [UnivLE.{max uX' vX', w}]
  [UnivLE.{max uS vS, w}] [UnivLE.{max uS' vS', w}]
variable (g' : ToposHom X X') (f' : ToposHom X' S')
  (f : ToposHom X S) (g : ToposHom S S')
variable [(SheafOfModules.restrictScalars g'.structureMap).IsRightAdjoint]
  [(SheafOfModules.restrictScalars f'.structureMap).IsRightAdjoint]
  [(SheafOfModules.restrictScalars f.structureMap).IsRightAdjoint]
  [(SheafOfModules.restrictScalars g.structureMap).IsRightAdjoint]
variable [HasModulePullbackDerived g'] [HasModulePullbackDerived g]
  [HasModulePullbackDerived f] [HasModulePullbackDerived f']
  [HasModulePushforwardDerived f] [HasModulePushforwardDerived f']
  [HasModuleDerivedAdjunction f] [HasModuleDerivedAdjunction f']
variable (squareIso : g.modulePullbackDerived ⋙ f.modulePullbackDerived ≅
  f'.modulePullbackDerived ⋙ g'.modulePullbackDerived)

/-- The derived base-change mate with ordinary coefficients, followed by direct image of the derived-to-ordinary counit. -/
def mapToOrdinary (F' : RingedSite.ModuleCat.{w} X') :=
  let coefficient := (HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} X') (0 : ℤ)).obj F'
  let K := (Hom.moduleLocalization.{w} X').obj coefficient
  let comparison := (Functor.totalLeftDerivedCounit (modulePullbackToDerived g')
    (Hom.moduleLocalization.{w} X') (Hom.ModuleQis.{w} X')).app coefficient
  CategoryTheory.DerivedBaseChange.app f'.moduleDerivedAdjunction f.moduleDerivedAdjunction
    squareIso K ≫ f.modulePushforwardDerived.map comparison

/-- The ordinary-coefficient base-change morphism is the mate followed by the canonical coefficient comparison. -/
theorem mapToOrdinary_spec (F' : RingedSite.ModuleCat.{w} X') :
    mapToOrdinary g' f' f g squareIso F' =
      let coefficient := (HomotopyCategory.singleFunctor (RingedSite.ModuleCat.{w} X') (0 : ℤ)).obj F'
      let K := (Hom.moduleLocalization.{w} X').obj coefficient
      CategoryTheory.DerivedBaseChange.app f'.moduleDerivedAdjunction f.moduleDerivedAdjunction
        squareIso K ≫ f.modulePushforwardDerived.map
          ((Functor.totalLeftDerivedCounit (modulePullbackToDerived g')
            (Hom.moduleLocalization.{w} X') (Hom.ModuleQis.{w} X')).app coefficient) := sorry

end RingedSite.ToposHom.DerivedBaseChange
