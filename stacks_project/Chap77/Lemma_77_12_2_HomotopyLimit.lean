/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FormalSystem.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.HomotopyLimit
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Definition
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Example_75_19_5_HomotopyLimit
public import stacks_project.Chap75.Lemma_75_19_1_Instances
public import stacks_project.Chap77.Situation_77_12_1_FormalSystem

/-!
# Homotopy limits of pushed stage sheaves

Typed checks of stage pushforward and the general quasi-coherent homotopy-limit API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.pushforwardModule : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
    S.space.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.ProperFlatFormalSystem.pushforwardModule_spec : ∀ (S : ProperFlatFormalSystem) (n : ℕ),
    S.pushforwardModule n = (Modules.pushforward (S.stageToSpace n)).obj (S.moduleSheaf n))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_homotopyLimit_isBounded : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X)
    (hK : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K),
    ((DerivedQCoh.inclusion X).rightAdjoint.obj K).obj.IsGE 0 ∧
      DerivedCategory.IsBoundedAbove ((DerivedQCoh.inclusion X).rightAdjoint.obj K).obj)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightAdjoint_isHomotopyLimit : ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (F : SequentialInverseSystem (QCoh X)) (K : ModuleDerived X)
    (hK : HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ)) K),
    HomotopyLimit.IsOf
      (F ⋙ QCoh.inclusion X ⋙ DerivedCategory.singleFunctor (Modules X) (0 : ℤ) ⋙
        (DerivedQCoh.inclusion X).rightAdjoint)
      ((DerivedQCoh.inclusion X).rightAdjoint.obj K))
