/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap75.Lemma_75_26_6_Pullback
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RestrictToScheme.LeftDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorAmplitude
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.RankLocus

/-! # Compatibility for derived restriction and Tor-amplitude

The conditional total left-derived restriction, Tor-amplitude, and rank-locus
existence theorem are provided by their mathematical library owners.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.restrictToSchemeDerived :
  ∀ {S : Scheme.{u}} (U : Over S),
    [(Functor.Homotopy.toDerived (Modules.restrictToScheme U)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules (ofOver U)) (ComplexShape.up ℤ))] →
    ModuleDerived (ofOver U) ⥤ DerivedCategory U.left.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeIn :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S},
    [DerivedCategory.DerivedTensor.Right.Has (C := X.Modules)] →
    ModuleDerived X → ℤ → ℤ → Prop)
