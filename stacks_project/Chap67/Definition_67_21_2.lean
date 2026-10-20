/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.21.2: a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is
quasi-affine if for every affine scheme `Z` and morphism `Z ⟶ Y`, the fibre product
`X ×_Y Z` is representable by a quasi-affine scheme. -/
@[stacks 03WL] #check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}, (X ⟶ Y) → Prop)
