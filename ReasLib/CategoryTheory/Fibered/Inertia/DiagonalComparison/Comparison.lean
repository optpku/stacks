/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Comparison.Computations

/-!
# Relative inertia comparison

Compatibility aggregate for the canonical relative-inertia comparison and its projection
computations. New users can import `Comparison.Construction.Basic` for the neutral
`BasedFunctor.RelativeInertia.diagonalComparisonObj` owner,
`Comparison.Construction.Naturality` for the bundled comparison and square equations, or
`Comparison.Construction.Computations` for projection readouts.  The `Comparison.Construction` and
`Comparison.Computations` paths remain aggregate entry points.
-/
