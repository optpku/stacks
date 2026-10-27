/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth.LciPlus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Points.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smoothing

/-!
# Density of smooth curves

The image of smooth families of curves is open and dense in the point space of
local complete intersection families with isolated singularities.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Smooth families of curves form an open subset of the point space of local
complete intersection families with isolated singularities. -/
theorem isOpen_smoothPointsSet (S : Scheme.{u}) : IsOpen (smoothPointsSet S) :=
  sorry

/-- Smooth families of curves are dense in the point space of local complete
intersection families with isolated singularities. -/
theorem dense_smoothPointsSet (S : Scheme.{u}) : Dense (smoothPointsSet S) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
