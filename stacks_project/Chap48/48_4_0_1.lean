/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.QcqsSquare
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 48.4.0.1: A cartesian square whose four scheme vertices are quasi-compact and
quasi-separated. -/
@[stacks 0A9J] #check
  (AlgebraicGeometry.IsQcqsPullbackSquare :
    {X' X Y' Y : AlgebraicGeometry.Scheme.{u}} →
      (X' ⟶ X) → (X' ⟶ Y') → (X ⟶ Y) → (Y' ⟶ Y) → Prop)
