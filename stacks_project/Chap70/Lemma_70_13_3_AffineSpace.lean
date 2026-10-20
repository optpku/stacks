module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace

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

#check (AlgebraicGeometry.AlgebraicSpace.affineOfScheme :
  (n : Type u) → (S : Scheme.{u}) → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.affineOfScheme_spec :
  ∀ (n : Type u) (S : Scheme.{u}),
    affineOfScheme n S = ofOver (Over.mk (AlgebraicGeometry.AffineSpace n S ↘ S)))

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace :
  (n : Type u) → {S : Scheme.{u}} → AlgebraicSpace S → AlgebraicSpace S)

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace.spec :
  ∀ (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S),
    AffineSpace n X = product X (affineOfScheme n S))

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace.functorOfPoints_eq :
  ∀ (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S),
    (AffineSpace n X).functorOfPoints =
      (X.functorOfPoints ⨯ (affineOfScheme n S).functorOfPoints))

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace.toBase :
  (n : Type u) → {S : Scheme.{u}} → (X : AlgebraicSpace S) → AffineSpace n X ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace.toOfScheme :
  (n : Type u) → {S : Scheme.{u}} → (X : AlgebraicSpace S) →
    AffineSpace n X ⟶ affineOfScheme n S)

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace.toBase_eq :
  ∀ (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S),
    AffineSpace.toBase n X = productFst X (affineOfScheme n S))

#check (AlgebraicGeometry.AlgebraicSpace.AffineSpace.toOfScheme_eq :
  ∀ (n : Type u) {S : Scheme.{u}} (X : AlgebraicSpace S),
    AffineSpace.toOfScheme n X = productSnd X (affineOfScheme n S))

end AlgebraicGeometry.AlgebraicSpace
