/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-! # Reduced algebraic spaces

The canonical public owner defines reducedness by a reduced étale scheme atlas and records
its equivalent universal chart condition. This helper re-exports that unchanged interface.
-/

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsReduced :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
