module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Product

/-!
# Relative affine spaces over schemes and algebraic spaces

Finite-dimensional affine spaces over a scheme over `S` form objects of `Over S`
with their canonical relative projections.
Relative affine space over an algebraic space is its product with affine space over
the base scheme, realized through functors of points.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Affine `n`-space over a scheme `V` over `S`, viewed as an object of `Over S`. -/
def affineSpaceOver {S : Scheme.{u}} (V : Over S) (n : ℕ) : Over S :=
  Over.mk ((𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) ≫ V.hom)

/-- The underlying scheme of `affineSpaceOver V n` is affine `n`-space over `V`. -/
theorem affineSpaceOver_left {S : Scheme.{u}} (V : Over S) (n : ℕ) :
    (affineSpaceOver V n).left = 𝔸(ULift.{u} (Fin n); V.left) := sorry

/-- The structure morphism of `affineSpaceOver V n` is the composite of the
relative affine-space projection with `V ⟶ S`. -/
theorem affineSpaceOver_hom {S : Scheme.{u}} (V : Over S) (n : ℕ) :
    (affineSpaceOver V n).hom =
      (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) ≫ V.hom := sorry

namespace affineSpaceOver

/-- The relative projection `𝔸(n; V) ⟶ V` in `Over S`. -/
def proj {S : Scheme.{u}} (V : Over S) (n : ℕ) : affineSpaceOver V n ⟶ V :=
  Over.homMk (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left)

/-- The underlying scheme morphism of `proj V n` is the canonical affine-space
structure map over `V`. -/
theorem proj_left {S : Scheme.{u}} (V : Over S) (n : ℕ) :
    (proj V n).left = (𝔸(ULift.{u} (Fin n); V.left) ↘ V.left) := sorry

end affineSpaceOver

/-- Affine `n`-space over a scheme `S`, viewed as an algebraic space over `S`. -/
def affineOfScheme (n : Type u) (S : Scheme.{u}) : AlgebraicSpace S :=
  ofOver (Over.mk (AlgebraicGeometry.AffineSpace n S ↘ S))

/-- The algebraic space `affineOfScheme n S` is `ofOver` of the structure morphism of
scheme-level affine space. -/
theorem affineOfScheme_spec (n : Type u) (S : Scheme.{u}) :
    affineOfScheme n S = ofOver (Over.mk (AlgebraicGeometry.AffineSpace n S ↘ S)) :=
  sorry

/-- Affine `n`-space over an algebraic space `X` over `S`, as the fibre product
`X ×_S A^n_S` of functors of points. -/
def AffineSpace (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) : AlgebraicSpace S :=
  product X (affineOfScheme n S)

namespace AffineSpace

/-- The algebraic space `AffineSpace n X` is the binary product of `X` with affine space
over the base scheme. -/
theorem spec (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineSpace n X = product X (affineOfScheme n S) :=
  sorry

/-- The functor of points of `AffineSpace n X` is the binary product of the functors of
points of `X` and of `A^n_S`. -/
theorem functorOfPoints_eq (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (AffineSpace n X).functorOfPoints =
      (X.functorOfPoints ⨯ (affineOfScheme n S).functorOfPoints) :=
  sorry

/-- The structure morphism `A^n_X ⟶ X`. -/
def toBase (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineSpace n X ⟶ X :=
  productFst X (affineOfScheme n S)

/-- The projection `A^n_X ⟶ A^n_S`. -/
def toOfScheme (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    AffineSpace n X ⟶ affineOfScheme n S :=
  productSnd X (affineOfScheme n S)

/-- The structure morphism of `AffineSpace n X` is the first product projection. -/
theorem toBase_eq (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toBase n X = productFst X (affineOfScheme n S) :=
  sorry

/-- The projection of `AffineSpace n X` to affine space over the base scheme is the
second product projection. -/
theorem toOfScheme_eq (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S) :
    toOfScheme n X = productSnd X (affineOfScheme n S) :=
  sorry

end AffineSpace

end AlgebraicGeometry.AlgebraicSpace
