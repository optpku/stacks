/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.SmoothChart

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.SmoothSchemeChart :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    AlgebraicGeometry.AlgebraicStack.Points X → Type (u + 1))

#check (AlgebraicGeometry.AlgebraicStack.SmoothSchemeChart.localRingDimDiff :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {x : AlgebraicGeometry.AlgebraicStack.Points X},
    AlgebraicGeometry.AlgebraicStack.SmoothSchemeChart x → EInt)
