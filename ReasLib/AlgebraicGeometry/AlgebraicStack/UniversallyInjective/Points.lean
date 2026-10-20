module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Lifting

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

/-- A universally injective morphism of algebraic stacks lifts an
algebraically closed field-valued point whose associated point lies in its
image, over the same field and up to a 2-isomorphism. -/
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

end AlgebraicGeometry.AlgebraicStack.UniversallyInjective
