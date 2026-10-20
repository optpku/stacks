/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernClass

@[expose] public section

open CategoryTheory

universe u

/- Remark 42.56.4: Total Chern classes give the canonical map from
vector-bundle `K₀` to the completed product of nonnegative Chow-cohomology degrees. -/
@[stacks 0FEL] #check
  (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p],
      AlgebraicGeometry.ChernClass.Theory δ p →
        AlgebraicGeometry.Scheme.VectorBundleK0 X →
          AlgebraicGeometry.ChowCohomology.Nonnegative.Completion δ p)

/- On a vector-bundle generator, the map is the whole family of Chern-class components. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass_of :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (E : CategoryTheory.ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree :
          CategoryTheory.ObjectProperty X.Modules)),
      AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes
          (CategoryTheory.ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree :
              CategoryTheory.ObjectProperty X.Modules) E) =
        AlgebraicGeometry.Scheme.VectorBundleK0.totalChernValue δ p classes E)

/- Addition in vector-bundle `K₀` is sent to convolution
multiplication of completed total Chern classes. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass_add :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (a b : AlgebraicGeometry.Scheme.VectorBundleK0 X),
      AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes (a + b) =
        AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes a *
          AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes b)

/- A negative generator is sent to the formal inverse of
its total Chern class. -/
#check
  (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass_neg_of :
    ∀ {S X : AlgebraicGeometry.Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [AlgebraicGeometry.UniversallyCatenary S] [IsDimensionFunction δ]
      [AlgebraicGeometry.LocallyOfFiniteType p]
      (classes : AlgebraicGeometry.ChernClass.Theory δ p)
      (E : CategoryTheory.ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree :
          CategoryTheory.ObjectProperty X.Modules)),
      AlgebraicGeometry.Scheme.VectorBundleK0.totalChernClass δ p classes
          (-CategoryTheory.ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree :
              CategoryTheory.ObjectProperty X.Modules) E) =
        AlgebraicGeometry.ChowCohomology.Nonnegative.Completion.formalInverse δ p
          (AlgebraicGeometry.Scheme.VectorBundleK0.totalChernValue δ p classes E))
