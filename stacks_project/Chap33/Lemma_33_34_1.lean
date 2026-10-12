/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.Variety

universe u

/- Lemma 33.34.1 (1): standard projective `n`-space over a field is a projective variety. -/
@[stacks 0B2P] #check
  (AlgebraicGeometry.ProjectiveSpace.schemeOver_projectiveVariety :
    ∀ (k : Type u) [Field k] (n : ℕ),
      AlgebraicGeometry.ProjectiveVariety
        (AlgebraicGeometry.ProjectiveSpace.schemeOver k n))

/- Lemma 33.34.1 (2): standard projective `n`-space over a field is a smooth variety. -/
@[stacks 0B2P] #check
  (AlgebraicGeometry.ProjectiveSpace.schemeOver_smoothVariety :
    ∀ (k : Type u) [Field k] (n : ℕ),
      AlgebraicGeometry.SmoothVariety
        (AlgebraicGeometry.ProjectiveSpace.schemeOver k n))

/- Lemma 33.34.1 (3): standard projective `n`-space over a field has dimension `n`. -/
@[stacks 0B2P] #check
  (AlgebraicGeometry.ProjectiveSpace.topologicalKrullDim_scheme_eq :
    ∀ (k : Type u) [Field k] (n : ℕ),
      topologicalKrullDim (AlgebraicGeometry.ProjectiveSpace.scheme k n) = n)
