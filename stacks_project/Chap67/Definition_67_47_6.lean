/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalMap.Dominant
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Definition 67.47.6: Let `S` be a scheme. Let `X` and `Y` be algebraic spaces over `S`.
Assume `|X|` and `|Y|` are irreducible. A rational map from `X` to `Y` is called dominant if
any representative `f : U ⟶ Y` is a dominant morphism in the sense of Definition 67.18.1. -/
@[stacks 0EMS] #check (AlgebraicGeometry.AlgebraicSpace.RationalMap.IsDominant :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {X Y : AlgebraicGeometry.AlgebraicSpace S} →
      AlgebraicGeometry.AlgebraicSpace.RationalMap X Y → Prop)
