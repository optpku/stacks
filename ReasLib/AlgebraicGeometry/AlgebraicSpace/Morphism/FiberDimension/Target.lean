/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Fiber

/-!
# Target-indexed fibre dimensions of morphisms of algebraic spaces

The fibre dimension of a morphism of algebraic spaces at a point of the
target is the supremum of the source-indexed relative dimensions along the
set-theoretic fibre. It is `⊥` off the image of the map on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fibre dimension of a morphism `f : X ⟶ Y` of algebraic spaces at a
point of `Y`, as the supremum of the relative dimensions of `f` at points of
the set-theoretic fibre. -/
noncomputable def fiberDimension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Points Y → WithBot ℕ∞ :=
  fun y ↦ ⨆ x ∈ fiberOver f y, fiberDimensionAt f x

/-- Evaluating `fiberDimension f` at a point of `Y` is the supremum of
`fiberDimensionAt f` over the set-theoretic fibre. -/
theorem fiberDimension_apply {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) :
    fiberDimension f y = ⨆ x ∈ fiberOver f y, fiberDimensionAt f x :=
  sorry

/-- The fibre dimension of `f` at `y` is `⊥` if and only if `y` is not in the
image of `Points.map f`. -/
theorem fiberDimension_eq_bot_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] (y : Points Y) :
    fiberDimension f y = ⊥ ↔ y ∉ Set.range (Points.map f) :=
  sorry

/-- The fibre dimension of `f` at `y` is at most `d` if and only if `f` has
relative dimension at most `d` at every point of `X` mapping to `y`. -/
theorem fiberDimension_le_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (y : Points Y) (d : ℕ) :
    fiberDimension f y ≤ (d : WithBot ℕ∞) ↔
      ∀ x ∈ fiberOver f y, RelativeDimensionLEAt f d x :=
  sorry

/-- For a finite type morphism of algebraic spaces, the fibre dimension at
the point represented by a field-valued point equals the dimension of the
corresponding field-valued fibre. -/
theorem fiberDimension_eq_dimension_fieldFiber {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (p : FieldValuedPoint Y) :
    fiberDimension f (Points.mk p) = dimension (fieldFiber f p) :=
  sorry

/-- The fibre dimension of a finite type morphism of algebraic spaces at any
point of its target is strictly less than infinity. -/
theorem fiberDimension_lt_top {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [FiniteType f] (y : Points Y) :
    fiberDimension f y < ⊤ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
