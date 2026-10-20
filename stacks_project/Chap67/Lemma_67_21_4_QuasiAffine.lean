/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine

/-!
# Canonical quasi-affine algebraic spaces and morphisms

Composition and base-change results use the object and morphism properties owned
by the reusable quasi-affine morphism module. This compatibility module retains
the existing import path while checking the canonical morphism predicate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}, (X ⟶ Y) → Prop)
