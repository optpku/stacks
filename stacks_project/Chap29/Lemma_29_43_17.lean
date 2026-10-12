/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.ProjComparison
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.43.17: if `f : X ⟶ S` is universally closed and `L` is relatively ample over
`f`, then the canonical comparison from `X` to the relative projective spectrum of the
pushforwards of the nonnegative tensor powers of `L` is an isomorphism. -/
@[stacks 0C6J] #check
  (AlgebraicGeometry.CanonicalRelativeProjComparison.isIso :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [RelativelyAmple f L] [UniversallyClosed f]
      (P : CanonicalRelativeProjComparison f L), IsIso P.comparison)
