/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import stacks_project.Chap103.Lemma_103_6_2
public import stacks_project.Chap103.Lemma_103_10_1
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage

/-! # Quasi-coherent direct images along quasi-compact quasi-separated morphisms

Typed compatibility checks for the canonical direct images and their
flat-base-change presentations, retaining prerequisite source exports.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory
universe u

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.directImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f], LQCohFbc X ⥤ LQCohFbc Y)

#check (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_eq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f],
    QCoh.directImage f =
      QCoh.toLQCohFbc X ⋙ LQCohFbc.directImage f ⋙ LQCohFbc.toQCoh Y)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.higherDirectImageFunctor_comp_lift :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ),
    Nonempty (LQCohFbc.higherDirectImageFunctor f i ⋙ LQCohFbc.inclusion Y ⋙
      ModuleUniverseComparison.lift Y ≅
        LQCohFbc.inclusion X ⋙ moduleHigherDirectImageFunctor f i))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.higherDirectImageFunctor_iso_lqcoh :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (i : ℕ),
    Nonempty (QCoh.higherDirectImageFunctor f i ≅
      QCoh.toLQCohFbc X ⋙ LQCohFbc.higherDirectImageFunctor f i ⋙ LQCohFbc.toQCoh Y))

#check (AlgebraicGeometry.GroupoidsOver.qCohHigherDirectImage_eq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)] (F : QCoh X) (i : ℕ),
    QCoh.higherDirectImage f F i = (QCoh.higherDirectImageFunctor f i).obj F)
