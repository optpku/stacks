/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory.Truncation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A compatible map from a derived module with quasi-coherent cohomology on an algebraic
space to a derived limit of its canonical lower-truncation tower is an isomorphism. -/
theorem lowerTruncationComparison_isIso {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : DerivedQCoh X) {K : ModuleDerived X} {c : E.obj ⟶ K}
    (hc : Lower.Comparison.Exists E.obj c) :
    IsIso c := sorry

end AlgebraicGeometry.AlgebraicSpace
