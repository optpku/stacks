/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.VectorBundle.ChernCharacter

open AlgebraicGeometry CategoryTheory

universe u

/- The Chern-character compatibility module exposes the canonical ring homomorphism. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p),
    AlgebraicGeometry.Scheme.VectorBundleK0 X →+*
      ChowCohomology.Nonnegative.RationalCompletion δ p)

/- The compatibility module also exposes the value on each vector-bundle generator. -/
#check (AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter_of :
  ∀ {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
    (classes : ChernClass.Theory δ p)
    (E : ObjectProperty.FullSubcategory
      (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules)),
    AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacter δ p classes
        (ObjectProperty.GrothendieckGroup.of
          (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.Modules) E) =
      AlgebraicGeometry.Scheme.VectorBundleK0.chernCharacterValue δ p classes E)
