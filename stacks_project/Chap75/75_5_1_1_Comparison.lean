/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Comparison

/-!
# Comparison for derived quasi-coherent modules on algebraic spaces

The weak-Serre inclusion `QCoh X ⥤ Modules X` induces the canonical unbounded
comparison `DerivedCategory (QCoh X) ⥤ DerivedQCoh X`.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.comparison X :
  DerivedCategory (QCoh X) ⥤ DerivedQCoh X)
