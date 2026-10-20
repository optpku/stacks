/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap65.Lemma_65_16_3_Equivalence
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap72.Lemma_72_14_3_GlobalSections
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_6_RankLocus

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.StructureSheaf

/-! # Structure-sheaf pushforward compatibility

The structure module, fibrewise global-sections condition, and proper-flat
pushforward results are provided by their mathematical library owners.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.structureSheafDerived :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), ModuleDerived X)

#check (AlgebraicGeometry.AlgebraicSpace.pushforwardStructureSheafDerived :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y), ModuleDerived Y)

#check (AlgebraicGeometry.AlgebraicSpace.fiberGlobalSectionsBijective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.fiberGlobalSectionsBijective_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    fiberGlobalSectionsBijective f ↔
      ∀ p : FieldValuedPoint Y, Function.Bijective (globalSectionsMap (fiberOverField f p)))

#check (AlgebraicGeometry.AlgebraicSpace.Hom.unitToPushforward_isIso_of_fiberGlobalSections :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Proper f] [Flat f] [FinitePresentation f],
    fiberGlobalSectionsBijective f → IsIso (IdealSubobject.unitToPushforward f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.structureSheafMap_isIso_of_fiberGlobalSections :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      fiberGlobalSectionsBijective f → IsIso (structureSheafMap f))

#check
  (AlgebraicGeometry.AlgebraicSpace.Hom.baseChange_structureSheafMap_isIso_of_fiberGlobalSections :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f],
      fiberGlobalSectionsBijective f →
        ∀ g : Y' ⟶ Y, IsIso (structureSheafMap (pullback.snd f g)))

#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_etale_structureSheafPushforward_decomposition :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f]
      (hΓ : fiberGlobalSectionsBijective f) (y : Points Y),
      ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y) (y' : Points Y')
        (hg : AlgebraicSpace.Etale g) (hy : Points.map g y' = y),
        ∃ P : ModuleDerived Y',
          ModuleDerived.IsPerfect P ∧
            CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeGE (C := Y'.Modules) P 1 ∧
            IsIsomorphic ((ModuleDerived.pullback g).obj
                (pushforwardStructureSheafDerived f))
              (structureSheafDerived Y' ⊞ P))
