/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.LocalRingAtPoint

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicStack.localRingDimAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] (x : AlgebraicStack.Points X),
    AlgebraicStack.IsFiniteTypePoint x → EInt)
