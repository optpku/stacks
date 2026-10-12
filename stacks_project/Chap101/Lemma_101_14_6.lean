/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap101.Definition_101_14_2_UniversallyInjective

/-!
# Algebraically closed point lifting for universally injective morphisms

A universally injective morphism of algebraic stacks lifts algebraically
closed field-valued points of the target whenever the associated point lies
in the image of the induced map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.UniversallyInjective

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Lemma 101.14.6: Let `f : X ⟶ Y` be a universally injective morphism of
algebraic stacks. Let `y : Spec(k) ⟶ Y` be a morphism where `k` is an
algebraically closed field. If the associated point of `y` lies in the image
of `Points.map f`, then there is a morphism `x : Spec(k) ⟶ X` with
`Nonempty (x ≫ f ≅ y)`. -/
@[stacks 0DTM]
theorem exists_algClosed_lift {f : X ⟶ Y} [UniversallyInjective f]
    {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (hy : Points.mk (FieldValuedPoint.of k σ y) ∈ Set.range (Points.map f)) :
    ∃ x : GroupoidsOver.slice (Over.mk σ) ⟶ X, Nonempty (x ≫ f ≅ y) :=
  sorry

/-- A universally injective morphism of algebraic stacks lifts an algebraically
closed field-valued point of the target if and only if the associated point
lies in the image of `Points.map f`. -/
theorem exists_algClosed_lift_iff {f : X ⟶ Y} [UniversallyInjective f]
    {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y) :
    Points.mk (FieldValuedPoint.of k σ y) ∈ Set.range (Points.map f) ↔
      ∃ x : GroupoidsOver.slice (Over.mk σ) ⟶ X, Nonempty (x ≫ f ≅ y) :=
  sorry

/-- Any 2-iso lift of a field-valued point along a morphism of algebraic
stacks implies that the associated point of the target lies in the image of
`Points.map f`. -/
theorem mem_range_points_map_of_iso {f : X ⟶ Y} {k : Type u} [Field k]
    (σ : Spec (.of k) ⟶ S) (y : GroupoidsOver.slice (Over.mk σ) ⟶ Y)
    (x : GroupoidsOver.slice (Over.mk σ) ⟶ X)
    (hxy : Nonempty (x ≫ f ≅ y)) :
    Points.mk (FieldValuedPoint.of k σ y) ∈ Set.range (Points.map f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.UniversallyInjective
