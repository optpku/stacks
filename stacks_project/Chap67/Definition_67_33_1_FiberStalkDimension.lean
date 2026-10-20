/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberStalkDimension

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.33.1: the pointwise fibre-stalk dimension
predicate for morphisms of algebraic spaces, including infinite values. -/
#check (AlgebraicGeometry.AlgebraicSpace.FiberStalkDimEqAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
    (X ⟶ Y) → ℕ∞ → AlgebraicSpace.Points X → Prop)
