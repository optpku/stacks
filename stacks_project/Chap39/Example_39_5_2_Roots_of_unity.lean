/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.RootsOfUnity.GroupScheme

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.MonObj TensorProduct

universe u

/-
Example 39.5.2 (Roots of unity) (1): For positive `n`, the functor of `n`th roots of
unity over `Spec(ULift ℤ)` is represented by the affine quotient scheme `overInt n`.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.functorOfPointsRepresentableBy.{u} :
    (n : ℕ) → [NeZero n] →
      (AlgebraicGeometry.RootsOfUnity.functorOfPoints
          (Spec (CommRingCat.of (ULift.{u} ℤ))) n ⋙ forget CommGrpCat).RepresentableBy
        (AlgebraicGeometry.RootsOfUnity.overInt.{u} n))

/-
Example 39.5.2 (Roots of unity) (2): The representing affine scheme is
`Spec((ULift ℤ)[X] ⧸ (X ^ n - 1))`.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.groupScheme_left :
    ∀ (n : ℕ) [NeZero n],
      (AlgebraicGeometry.RootsOfUnity.groupScheme.{u} n).X.left =
        Spec (CommRingCat.of (AlgebraicGeometry.RootsOfUnity.coordinateRing.{u} n)))

/-
Example 39.5.2 (Roots of unity) (3): The integral roots-of-unity scheme is a
commutative group scheme.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.groupScheme :
    (n : ℕ) → [NeZero n] →
      CommGrp (Over (Spec (CommRingCat.of (ULift.{u} ℤ)))))

/-
Example 39.5.2 (Roots of unity) (4): Multiplication is dual to the coordinate-ring
map sending `X` to `X ⊗ₜ X`.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.mul_eq_specMap_comul :
    ∀ (n : ℕ) [NeZero n],
      μ[AlgebraicGeometry.RootsOfUnity.overInt.{u} n].left =
        (AlgebraicGeometry.pullbackSpecIso (ULift.{u} ℤ)
          (AlgebraicGeometry.RootsOfUnity.coordinateRing.{u} n)
          (AlgebraicGeometry.RootsOfUnity.coordinateRing.{u} n)).hom ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom
              (AlgebraicGeometry.RootsOfUnity.CoordinateRing.comul.{u} n)))

/-
Example 39.5.2 (Roots of unity) (5): Base change to any scheme `S` is a
commutative group scheme over `S`.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.baseChange :
    (n : ℕ) → [NeZero n] → (S : Scheme.{u}) → CommGrp (Over S))

/-
Example 39.5.2 (Roots of unity) (6): The points of the base-changed group scheme
are the `n`th roots of unity in global sections.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.BaseChange.homMulEquiv :
    (n : ℕ) → [NeZero n] → (S : Scheme.{u}) → (T : Over S) →
      (T ⟶ (AlgebraicGeometry.RootsOfUnity.baseChange n S).X) ≃*
        rootsOfUnity n Γ(T.left, ⊤))

/-
Example 39.5.2 (Roots of unity) (7): The base-changed affine scheme represents the
roots-of-unity functor over `S`.
-/
@[stacks 040M] #check
  (AlgebraicGeometry.RootsOfUnity.BaseChange.representableBy :
    (n : ℕ) → [NeZero n] → (S : Scheme.{u}) →
      (AlgebraicGeometry.RootsOfUnity.functorOfPoints S n ⋙ forget CommGrpCat).RepresentableBy
        (AlgebraicGeometry.RootsOfUnity.baseChange n S).X)
