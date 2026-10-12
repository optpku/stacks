/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial

universe u

/-
Lemma 33.35.14: For a coherent module `ℱ` on standard projective `n`-space over a field `k`,
the Euler-characteristic function of its canonical twists is a numerical polynomial.
-/
@[stacks 08AC] #check
  (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_isNumericalPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      IsNumericalPolynomial
        (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial k n ℱ))
