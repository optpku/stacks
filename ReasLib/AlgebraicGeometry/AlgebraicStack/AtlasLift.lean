/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Lifting smooth surjective scheme atlases along morphisms of algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks over a scheme lifts any prescribed smooth
surjective scheme atlas of its target to a smooth surjective scheme atlas of
its source, with a scheme-induced upper arrow and a 2-commutative square. -/
@[stacks 04T1]
theorem exists_smoothSurjective_atlas_lift {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {V : Over S}
    (y : GroupoidsOver.slice V ⟶ Y) (hy_smooth : Groupoids.Hom.Smooth y)
    (hy_surj : Groupoids.Hom.Surjective y) :
    ∃ (U : Over S) (α : U ⟶ V) (x : GroupoidsOver.slice U ⟶ X),
      Nonempty (x ≫ f ≅ overMap α ≫ y) ∧
        Groupoids.Hom.Smooth x ∧ Groupoids.Hom.Surjective x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
