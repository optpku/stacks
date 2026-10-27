/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleFppfComparison
public import stacks_project.Chap84.Lemma_84_7_1_Carrier
public import stacks_project.Chap84.Lemma_84_7_1_Ringed

@[expose] public section

open CategoryTheory RingedSite RingedSite.Hom

universe uX vX uY vY w z

#check (RingedSite.Hom.ordinaryToRightDerived :
  ∀ {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
    (f : RingedSite.Hom X Y)
    [UnivLE.{max uX vX, z}] [UnivLE.{max uY vY, z}]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived.{z} f) (ModuleQis.{z} X)]
    (F : ModuleCat.{z} X) (G : ModuleCat.{z} Y)
    (h : G ⟶ (modulePushforward.{z} f).obj F),
    (moduleLocalization.{z} Y).obj ((HomotopyCategory.singleFunctor Y.ModuleCat 0).obj G) ⟶
      (modulePushforwardDerived.{z} f).obj
        ((moduleLocalization.{z} X).obj ((HomotopyCategory.singleFunctor X.ModuleCat 0).obj F)))
