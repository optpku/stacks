/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.43.10: A projective morphism is quasi-projective. -/
@[stacks 07RL] #check
  (AlgebraicGeometry.Projective.toQuasiProjective :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Projective f → AlgebraicGeometry.QuasiProjective f)
