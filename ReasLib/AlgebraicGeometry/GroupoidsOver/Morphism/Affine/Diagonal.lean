/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Affine permanence for morphisms of algebraic stacks

An affine composite of morphisms of algebraic stacks may be cancelled when
the second morphism has affine relative diagonal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open FiberedCategoryOver.Groupoids.Hom (diagonal)
open scoped Bicategory

universe u

noncomputable section

namespace AlgebraicGeometry.Groupoids.Hom
namespace Affine

/-- If a composite of morphisms of algebraic stacks is affine and the second
morphism has affine relative diagonal, then the first morphism is affine. -/
@[stacks 0GQE]
theorem of_comp_of_affineDiagonal {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (b : Y ⟶ Z) [Affine (f ≫ b)]
    [Affine (diagonal.{u + 1, u, u + 1} b)] :
    Affine f :=
  sorry

end Affine
end AlgebraicGeometry.Groupoids.Hom
