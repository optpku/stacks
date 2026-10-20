/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictScalars.Pair

/-!
# Restriction-of-scalars pairs

A pair `(a, b)` for morphisms `X ⟶ Z ⟶ B` of algebraic spaces over a scheme
`S`, consisting of a morphism `a : T ⟶ B` and a morphism
`b : T ×_{a,B} Z ⟶ X` over `Z`.
-/

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RestrictScalars.Pair :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Z B : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Z) → (Z ⟶ B) → AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
