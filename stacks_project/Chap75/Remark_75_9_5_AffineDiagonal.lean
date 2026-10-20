/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.AbsoluteAffineDiagonal

/-!
# Absolute affine diagonal of algebraic spaces

An algebraic space has affine diagonal over the terminal scheme when the diagonal
of the space viewed over that scheme is a representable affine morphism.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyAffineDiagonal :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
