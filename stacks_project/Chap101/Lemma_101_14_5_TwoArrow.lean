/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Algebraically closed 2-arrow lifting

A morphism of algebraic stacks lifts 2-arrows between `Spec(k)`-points for
algebraically closed fields when every 2-iso after postcomposition with `f`
arises by whiskering a 2-iso of the points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- A morphism `f : X ⟶ Y` of algebraic stacks lifts 2-arrows between
`Spec(k)`-points for algebraically closed fields: for every algebraically
closed field `k`, structure map `σ : Spec (.of k) ⟶ S`, and 1-morphisms
`x1, x2` from the slice of `σ` to `X`, every 2-iso `x1 ≫ f ≅ x2 ≫ f` is
`whiskerRightIso α f` for some 2-iso `α : x1 ≅ x2`. -/
def liftsAlgClosedTwoArrows : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X),
    Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f)

/-- `liftsAlgClosedTwoArrows f` means whiskering 2-isos of algebraically closed
slice maps along `f` is surjective. -/
theorem liftsAlgClosedTwoArrows_iff : liftsAlgClosedTwoArrows f ↔
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
      (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X),
      Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f) :=
  sorry

namespace liftsAlgClosedTwoArrows

/-- Surjectivity of `whiskerRightIso (·) f` on algebraically closed slice maps
witnesses `liftsAlgClosedTwoArrows f`. -/
theorem of
    (h : ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
      (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X),
      Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f)) :
    liftsAlgClosedTwoArrows f :=
  sorry

/-- Under `liftsAlgClosedTwoArrows f`, whiskering 2-isos of algebraically closed
slice maps along `f` is surjective. -/
theorem spec (h : liftsAlgClosedTwoArrows f) {k : Type u} [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X) :
    Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f) :=
  sorry

/-- Under `liftsAlgClosedTwoArrows f`, every 2-iso `β : x1 ≫ f ≅ x2 ≫ f` of
algebraically closed slice maps is `whiskerRightIso α f` for some
`α : x1 ≅ x2`. -/
theorem exists_whisker (h : liftsAlgClosedTwoArrows f) {k : Type u} [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X)
    (β : x1 ≫ f ≅ x2 ≫ f) :
    ∃ α : x1 ≅ x2, β = whiskerRightIso α f :=
  sorry

end liftsAlgClosedTwoArrows

end AlgebraicGeometry.AlgebraicStack
