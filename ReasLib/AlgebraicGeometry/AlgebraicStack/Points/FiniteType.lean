/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-!
# Finite-type points of algebraic stacks

A point of an algebraic stack is represented by a locally-of-finite-type
morphism from the spectrum of a field if and only if it is the image of a
closed point under a smooth morphism from a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (x : Points X)

/-- There exists a scheme `U` over `S`, a closed point of `U`, and a smooth
morphism from `GroupoidsOver.slice U` to `X` sending that point to `x`. -/
def existsSmoothClosedPoint : Prop :=
  ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
    u ∈ closedPoints U.left ∧ Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x

/-- `existsSmoothClosedPoint x` means some smooth morphism
`φ : GroupoidsOver.slice U ⟶ X` from a scheme over `S` sends a closed point of
`U` to `x`. -/
theorem existsSmoothClosedPoint_iff :
    existsSmoothClosedPoint x ↔
      ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
        u ∈ closedPoints U.left ∧ Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x :=
  sorry

namespace existsSmoothClosedPoint

/-- A smooth morphism from a scheme over `S` sending a closed point to `x`
witnesses `existsSmoothClosedPoint x`. -/
theorem of {U : Over S} {u : U.left} {φ : GroupoidsOver.slice U ⟶ X}
    (hu : u ∈ closedPoints U.left) [Groupoids.Hom.Smooth φ]
    (hx : Points.mapSlice φ u = x) : existsSmoothClosedPoint x :=
  sorry

/-- `existsSmoothClosedPoint x` supplies a scheme over `S`, a closed point of
that scheme, and a smooth morphism to `X` sending the closed point to `x`. -/
theorem spec (h : existsSmoothClosedPoint x) :
    ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
      u ∈ closedPoints U.left ∧ Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x :=
  sorry

end existsSmoothClosedPoint

/-- A point of an algebraic stack has a locally-of-finite-type field-valued
representative if and only if it is the image of a closed point of a scheme
under a smooth morphism to the stack. -/
@[stacks 06FX]
theorem existsLocallyOfFiniteTypeFieldValuedPoint_iff_existsSmoothClosedPoint :
    (∃ p : FieldValuedPoint X, LocallyOfFiniteType p.hom ∧ Points.mk p = x) ↔
      existsSmoothClosedPoint x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
