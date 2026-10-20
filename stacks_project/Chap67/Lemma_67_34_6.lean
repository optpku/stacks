/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension.QuasiFinite

/-!
# Locally quasi-finite morphisms of algebraic spaces and relative dimension zero

A locally finite-type morphism of algebraic spaces is locally quasi-finite
exactly when it has relative dimension zero at every source point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.34.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. Then `f` is
locally quasi-finite if and only if `f` has relative dimension `0` at each
point of `|X|`. -/
@[stacks 04NV] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_iff_relativeDimension_zero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType f],
      AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite f ↔
        AlgebraicGeometry.AlgebraicSpace.RelativeDimension f 0)
