/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.Principality

@[expose] public section

universe u

/- Lemma 33.34.4: let `k` be a field and let `Z` be a closed subscheme of projective
`n`-space with no embedded points whose irreducible components all have dimension `n - 1`.
Then the homogeneous twist ideal corresponding to `Z` is principal. -/
@[stacks 0BXU] #check
  (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal_isPrincipal_of_noEmbeddedPoints_of_componentsHaveDimension :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (Z : (AlgebraicGeometry.ProjectiveSpace.scheme k n).IdealSheafData)
      (P : AlgebraicGeometry.ProjTwistPresentation
        (AlgebraicGeometry.ProjectiveSpace.grading k n)),
      Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme) →
      AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.ComponentsHaveDimension k n Z →
      (AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.twistIdeal n Z P).toIdeal.IsPrincipal)
