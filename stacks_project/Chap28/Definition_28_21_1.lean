/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 28.21.1 compatibility entry point

The locally projective scheme-module predicate is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic`.
-/

/- Definition 28.21.1

For a quasi-coherent `ℱ : X.Modules`, this predicate requires
`Module.Projective Γ(X, U) Γ(ℱ, U)` for every affine open `U` of `X`.
-/
@[stacks 05JP]
#check (AlgebraicGeometry.Scheme.Modules.IsLocallyProjective :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, X.Modules → Prop)
