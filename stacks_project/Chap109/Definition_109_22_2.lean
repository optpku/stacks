/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 109.22.2: a family of curves `f : X ⟶ S` is a stable family of
curves if it is prestable and, for every point `s` of `S`, the fibre `X_s`
has genus at least `2` and has neither a rational tail nor a rational bridge. -/
@[stacks 0E75] #check (AlgebraicGeometry.AlgebraicSpace.IsStableFamily :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → Prop)
