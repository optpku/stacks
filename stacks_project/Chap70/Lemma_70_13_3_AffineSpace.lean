module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_1_Product

/-!
# Relative affine space over an algebraic space

Affine `n`-space over an algebraic space `X` over a scheme `S` is the fibre product
`X ×_S A^n_S`, realized as the binary product of functors of points.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

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
