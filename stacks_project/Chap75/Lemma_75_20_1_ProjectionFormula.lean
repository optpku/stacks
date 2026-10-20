/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectTensorComparison

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Prod
public import ReasLib.Algebra.Homology.CochainComplex.Monoidal.Functor
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Bifunctor
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula
public import stacks_project.Chap75.Lemma_75_5_6_Tensor
public import stacks_project.Chap81.Lemma_81_10_5_Adjunction

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.ProjectionFormula

/-! # Projection formula on derived quasi-coherent modules

The shared mathematical owners supply the actual tensor comparisons and canonical adjunction
mate. The chapter imports retain the established source-facing pullback and pushforward exports.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

universe u

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.modulePullbackDerived_cochainCounit :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : CochainComplex (Modules Y) ℤ),
    (modulePullbackDerived f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj
        (((Modules.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.moduleDerivedPullbackTensorComparison :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y),
    (modulePullbackDerived f).obj
        ((DerivedTensor.Bifunctor.functor (C := Modules Y)).obj (A, B)) ⟶
      (DerivedTensor.Bifunctor.functor (C := Modules X)).obj
        ((modulePullbackDerived f).obj A, (modulePullbackDerived f).obj B))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.rightTensorComparison :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (A B : ModuleDerived Y),
    (modulePullbackDerived f).obj ((DerivedTensor.Right.functor B).obj A) ⟶
      (DerivedTensor.Right.functor ((modulePullbackDerived f).obj B)).obj
        ((modulePullbackDerived f).obj A))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.leftMate :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (E : ModuleDerived X) (K : ModuleDerived Y),
    (DerivedTensor.Right.functor K).obj ((Modules.pushforwardDerived f).obj E) ⟶
      (Modules.pushforwardDerived f).obj
        ((DerivedTensor.Right.functor ((modulePullbackDerived f).obj K)).obj E))

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.isIso_projectionFormula :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (E : DerivedQCoh X) (K : DerivedQCoh Y),
    IsIso (leftMate f E.obj K.obj))
