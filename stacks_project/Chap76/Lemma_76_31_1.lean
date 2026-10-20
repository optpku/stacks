/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberDimension.Target
import StacksCheckRecall

/-!
# Dimension of fibres of finite type morphisms of algebraic spaces

For a finite type morphism of algebraic spaces, the target-indexed fibre
dimension at a point equals the dimension of any field-valued fibre over a
representative of that point.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.31.1: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite type
morphism of algebraic spaces over `S`. Let `y` be a point of `Y`, represented
by a field-valued point `p`. Then the fibre dimension of `f` at `y` equals the
dimension of the algebraic space `fieldFiber f p`.

Quantity (1) is `fiberDimension f (Points.mk p)`, equal to `⊥` when
`Points.mk p` is not in the image of `Points.map f`, and otherwise the least
`d : ℕ` such that `f` has relative dimension at most `d` at every point of `X`
mapping to `y`. Quantity (2) is `dimension (fieldFiber f p)` for any
representative `p` of `y`. -/
@[stacks 0D4M] #check
  (AlgebraicGeometry.AlgebraicSpace.fiberDimension_eq_dimension_fieldFiber :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
      (p : FieldValuedPoint Y),
      fiberDimension f (Points.mk p) = dimension (fieldFiber f p))

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_eq_bot_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (y : Points Y), fiberDimension f y = ⊥ ↔ y ∉ Set.range (Points.map f))

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_le_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (y : Points Y) (d : ℕ),
    fiberDimension f y ≤ (d : WithBot ℕ∞) ↔
      ∀ x ∈ fiberOver f y, RelativeDimensionLEAt f d x)

#check (AlgebraicGeometry.AlgebraicSpace.fiberDimension_lt_top :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FiniteType f]
    (y : Points Y), fiberDimension f y < ⊤)
