/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

/-!
# Image membership from field-valued lifts

A field-valued point that admits a lift up to a 2-isomorphism lies in the
image of the induced map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Points

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- A field-valued point admitting a lift up to a 2-isomorphism along a
morphism of algebraic stacks lies in the image of the induced map on points. -/
theorem mem_range_map_of_iso {f : X ⟶ Y} {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (x : GroupoidsOver.slice (Over.mk σ) ⟶ X)
    (hxy : Nonempty (x ≫ f ≅ y)) :
    Points.mk (FieldValuedPoint.of k σ y) ∈ Set.range (Points.map f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Points
