/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq :
    {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.GroupoidsOver S} →
    [AlgebraicGeometry.AlgebraicStack X] →
    [AlgebraicGeometry.AlgebraicStack Y] → (X ⟶ Y) → Type (u + 1))
