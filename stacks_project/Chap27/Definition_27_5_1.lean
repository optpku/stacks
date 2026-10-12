/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry

section

variable (S : Scheme.{u}) (n : ℕ)

/- Definition 27.5.1: affine `n`-space over `S` is the scheme indexed by
`ULift.{u} (Fin n)`. -/
@[stacks 01M0] #check
  (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) S : AlgebraicGeometry.Scheme.{u})

/- The canonical projection makes affine `n`-space a scheme over `S`. -/
#check
  (AlgebraicGeometry.AffineSpace.over (ULift.{u} (Fin n)) S :
    AlgebraicGeometry.Scheme.CanonicallyOver
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) S) S)

end

section

variable (R : CommRingCat.{u}) (n : ℕ)

/- Over the affine base `Spec R`, affine `n`-space is canonically isomorphic to the spectrum of
the polynomial ring indexed by `ULift.{u} (Fin n)`. -/
#check
  (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin n)) R :
    CategoryTheory.Iso
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) (AlgebraicGeometry.Spec R))
      (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) R))))

end

end AlgebraicGeometry
