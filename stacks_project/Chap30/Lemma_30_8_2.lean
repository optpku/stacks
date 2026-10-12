/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.TwistCohomology.Naturality
import StacksCheckRecall

universe u

/- Lemma 30.8.2

For positive-dimensional standard projective space, the standard cohomology identifications for
twisting sheaves are compatible with arbitrary coefficient homomorphisms.  Multiplication by a
homogeneous polynomial is ordinary multiplication on degree-zero cohomology and the
contragredient multiplication map on top cohomology. -/
@[stacks 01XV] #check
  (AlgebraicGeometry.ProjectiveSpace.twistingSheaf.cohomology_naturality_sharedIdentifications :
    ∀ {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
      (n : ℕ) (_ : 0 < n) (d : ℤ) (m : ℕ)
      (f : MvPolynomial (Fin (n + 1)) R)
      (hf : f ∈ AlgebraicGeometry.ProjectiveSpace.grading R n m),
      ∃ (zeroIdent :
          AlgebraicGeometry.Scheme.Hom.cohomology
              (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
              (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) 0 ≅
            ModuleCat.of R (AlgebraicGeometry.ProjectiveSpace.gradedPiece R n d))
        (topIdent :
          AlgebraicGeometry.Scheme.Hom.cohomology
              (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
              (AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n d) n ≅
            ModuleCat.of R
              (AlgebraicGeometry.ProjectiveSpace.topCohomologyDual R n d)),
        AlgebraicGeometry.ProjectiveSpace.twistingSheaf.BaseChangeCompatibleWith
            φ n d zeroIdent topIdent ∧
          AlgebraicGeometry.ProjectiveSpace.twistingSheaf.MulCompatibleWith
            n d m f hf zeroIdent topIdent)
