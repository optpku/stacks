/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Thickening

open AlgebraicGeometry CategoryTheory

universe u

/- Theorem 41.15.2 (Une equivalence remarquable de catégories): if `i : S₀ ⟶ S`
is a thickening, base change along `i` is an equivalence from schemes étale over `S`
to schemes étale over `S₀`. -/
@[stacks 039R] #check
  (AlgebraicGeometry.Scheme.smallEtalePullback_isEquivalence_of_isThickening :
    ∀ {S₀ S : Scheme.{u}} (i : S₀ ⟶ S) [IsThickening i],
      (AlgebraicGeometry.Scheme.smallEtalePullback i).IsEquivalence)
