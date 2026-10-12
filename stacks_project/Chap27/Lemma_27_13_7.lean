/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 27.13.7: the degreewise kernels of restriction to a closed subscheme of standard
projective space form a homogeneous ideal whose localizations recover the subscheme on every
standard coordinate chart. -/
@[stacks 03GL] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal_spec :
    ∀ {R : Type u} [CommRing R]
      (n : ℕ)
      (Z : (AlgebraicGeometry.ProjectiveSpace.scheme R n).IdealSheafData)
      (P : AlgebraicGeometry.ProjTwistPresentation
        (AlgebraicGeometry.ProjectiveSpace.grading R n)),
      (∀ f : MvPolynomial (Fin (n + 1)) R,
        f ∈ AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal n Z P ↔
          AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Vanishes n Z P f) ∧
        AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.IdealSpec n Z
          (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal n Z P))
