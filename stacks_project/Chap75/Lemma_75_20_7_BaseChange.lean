/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Glueing

public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence
public import stacks_project.Chap75.Lemma_75_26_4_Pullback

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ChartRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.BaseChange

/-! # Compatibility imports for relative Tor-amplitude and chart restriction -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace ComplexShape

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.restrictToEtaleChart :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallEtaleSite X)
    [(Functor.Homotopy.toDerived
      (SmallEtaleModuleGlueing.restrictFunctor_hom U ⋙ Modules.restrictToScheme U.left ⋙
        Scheme.Modules.toRingedSpace U.left.left)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules X) (up ℤ))],
    ModuleDerived X ⥤ RingedSpace.ModuleDerived U.left.left.toRingedSpace)

#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.hasTorAmplitudeInOver_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (E : ModuleDerived X) (a b : ℤ),
    ModuleDerived.HasTorAmplitudeInOver f E a b ↔
      DerivedCategory.DerivedTensor.HasTorAmplitudeIn
        ((ModuleDerived.restrictToRelativeCoefficients f).obj E) a b)
