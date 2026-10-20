/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.FiniteType

/-!
# Finite-type points and smooth morphisms

The finite-type points of an algebraic stack are the images of closed points of
schemes under smooth morphisms, and the same description holds if those schemes
are required to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The finite-type points of an algebraic stack are the union of the images
of closed points of schemes under smooth morphisms to the stack. -/
@[stacks 06FZ]
theorem finiteTypePoints_eq_iUnion_image_closedPoints_smooth {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    finiteTypePoints X =
      ⋃ (U : Over S) (φ : GroupoidsOver.slice U ⟶ X) (_ : Groupoids.Hom.Smooth φ),
        Points.mapSlice φ '' closedPoints U.left :=
  sorry

/-- The finite-type points of an algebraic stack are the union of the images
of closed points of affine schemes under smooth morphisms to the stack. -/
@[stacks 06FZ]
theorem finiteTypePoints_eq_iUnion_image_closedPoints_affine_smooth
    {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    finiteTypePoints X =
      ⋃ (U : Over S) (_ : AlgebraicGeometry.IsAffine U.left)
        (φ : GroupoidsOver.slice U ⟶ X) (_ : Groupoids.Hom.Smooth φ),
        Points.mapSlice φ '' closedPoints U.left :=
  sorry

/-- Membership in `finiteTypePoints X` is equivalent to being the image of a
closed point under a smooth morphism from an affine scheme. -/
theorem mem_finiteTypePoints_iff_exists_affine_smooth_closedPoint
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] {x : Points X} :
    x ∈ finiteTypePoints X ↔
      ∃ (U : Over S) (u : U.left) (φ : GroupoidsOver.slice U ⟶ X),
        AlgebraicGeometry.IsAffine U.left ∧ u ∈ closedPoints U.left ∧
          Groupoids.Hom.Smooth φ ∧ Points.mapSlice φ u = x :=
  sorry

/-- The image of the closed points of a scheme under a smooth morphism to `X`
consists of finite-type points of `X`. -/
theorem mapSlice_image_closedPoints_subset_finiteTypePoints {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] {U : Over S}
    (φ : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth φ] :
    Points.mapSlice φ '' closedPoints U.left ⊆ finiteTypePoints X :=
  sorry

end AlgebraicGeometry.AlgebraicStack
