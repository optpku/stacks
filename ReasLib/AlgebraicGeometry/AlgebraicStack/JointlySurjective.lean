/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points

/-!
# Jointly surjective families of objects of algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- A family of objects `x i : U i ⟶ X` is jointly surjective when
`∐ x i : ∐ U i ⟶ X` is surjective on points of algebraic stacks. -/
def jointlySurjective {I : Type v} {U : I → Over S}
    (x : ∀ i, GroupoidsOver.slice (U i) ⟶ X) : Prop :=
  Function.Surjective
    (fun p : (i : I) × Points (GroupoidsOver.slice (U i)) ↦ Points.map (x p.1) p.2)

/-- Joint surjectivity of a family of objects is equivalent to every point of
`X` lying in the image of some `Points.map (x i)`. -/
theorem jointlySurjective_iff {I : Type v} {U : I → Over S}
    (x : ∀ i, GroupoidsOver.slice (U i) ⟶ X) :
    jointlySurjective x ↔ ∀ y : Points X, ∃ i, y ∈ Set.range (Points.map (x i)) := sorry

end AlgebraicGeometry.AlgebraicStack
