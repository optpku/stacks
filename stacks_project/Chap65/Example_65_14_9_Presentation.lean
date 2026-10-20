/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.Presentation

@[expose] public section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.preRelation :
  ∀ (k : Type u) [Field k],
    AlgebraicGeometry.Scheme.PreRelation (AlgebraicGeometry.AlgebraicSpace.InfiniteProduct.cover k))
