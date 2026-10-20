/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Subobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap71.Lemma_71_2_1_Pullback

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal

/-!
# Fitting ideals of modules on algebraic spaces

Typed checks of the canonical Fitting-ideal construction and its affine étale
characterization.
-/

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) (i : ℕ),
    IdealSubobject X)

#check (AlgebraicGeometry.AlgebraicSpace.fittingIdealSheaf_affineEtale :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ) (U : affineEtaleSite X),
    SheafOfModules.Subobject.sections (fittingIdealSheaf F i) (op U.obj) =
      (affineChartFittingIdeal F i U).comap (affineEtaleRestrict U (𝟙 U.obj)))
