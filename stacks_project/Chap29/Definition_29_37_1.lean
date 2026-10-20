/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
import StacksCheckRecall

@[expose] public section

/-!
# Definition 29.37.1

The reusable relative-ampleness owner is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative`.
-/

universe u

/- Definition 29.37.1: An invertible module on `X` is relatively ample over `f : X ⟶ S`
when `f` is quasi-compact and its restriction to the preimage of every affine open of `S` is
ample. -/
@[stacks 01VH] #check
  (AlgebraicGeometry.RelativelyAmple :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}, (X ⟶ S) → X.Modules → Prop)
