/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Dimension along integral morphisms of algebraic spaces

An integral morphism of algebraic spaces cannot increase global dimension, in
the sense of `AlgebraicSpace.dimension`. If the morphism is also surjective,
the dimensions agree.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The dimension of the source of an integral morphism of algebraic spaces is
at most the dimension of its target. -/
@[stacks 0EDB]
theorem dimension_le_of_isIntegralHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsIntegralHom f] :
    dimension X ≤ dimension Y :=
  sorry

/-- A surjective integral morphism of algebraic spaces preserves dimension. -/
@[stacks 0EDB]
theorem dimension_eq_of_surjective_isIntegralHom {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f] [Surjective f] :
    dimension X = dimension Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
