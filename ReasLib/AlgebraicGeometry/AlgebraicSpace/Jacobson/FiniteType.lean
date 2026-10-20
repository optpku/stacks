/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Locally of finite type over Jacobson algebraic spaces

A morphism of algebraic spaces that is locally of finite type into a Jacobson
target has Jacobson source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace LocallyOfFiniteType

/-- A locally-of-finite-type morphism of algebraic spaces with Jacobson target has
Jacobson source. -/
theorem isJacobson {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsJacobson Y] : IsJacobson X :=
  sorry

end LocallyOfFiniteType

end AlgebraicGeometry.AlgebraicSpace
