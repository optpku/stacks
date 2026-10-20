/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranch

/-!
# Geometric unibranchness of algebraic spaces

The pointwise and global predicates are provided by the canonical mathematical owner.
-/

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.GeometricallyUnibranchAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
    AlgebraicGeometry.AlgebraicSpace.Points X → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.IsGeometricallyUnibranch :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Prop)
