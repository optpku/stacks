/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Dominant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField.Units

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- The raw flat-pullback construction formerly exposed by this compatibility module. -/
#check (AlgebraicGeometry.AlgebraicCycle.flatPullback :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (c : AlgebraicCycle Y.left ℤ), AlgebraicCycle X.left ℤ)
