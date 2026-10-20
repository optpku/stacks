/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.RelativeDiagonal
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Comparison
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Inverse
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Equivalence

/-!
# Fixed-owner inertia projection comparison

Aggregate for the relative diagonal, its relative-inertia comparison, explicit
inverse, and bicategorical equivalence in the fixed fibred-category owner.
The preferred surface consists of
`FiberedCategoryOver.RelativeInertia.{relativeDiagonal,diagonalComparison,
diagonalComparison.inverse,diagonalComparisonEquivalence}`. Their computation APIs live under
lowercase role namespaces such as `.obj`, `.map`, `.aut`, `.unit`, and `.counit`.
-/

@[expose] public section
