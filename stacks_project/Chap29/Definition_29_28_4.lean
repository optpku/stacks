/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension

@[expose] public section

/-!
# Definition 29.28.4

The reusable local fibre-dimension API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension`.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 29.28.4: The local dimension of a scheme-theoretic fibre at a source point. -/
#check (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X), WithBot ℕ∞)
#check (AlgebraicGeometry.Scheme.Hom.fiberDimensionAt_eq_topologicalKrullDimAt_asFiber :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    f.fiberDimensionAt x = topologicalKrullDimAt (f.asFiber x))
#check AlgebraicGeometry.Scheme.Hom.fiberDimensionLELocus
#check AlgebraicGeometry.Scheme.Hom.mem_fiberDimensionLELocus
