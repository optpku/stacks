/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.UniversalHomeomorphism

universe u

/- Lemma 29.45.6: for every scheme `X`, the canonical closed immersion from its reduction
`Scheme.reductionι X : Scheme.reduction X ⟶ X` is a universal homeomorphism. -/
@[stacks 054M] #check
  (AlgebraicGeometry.Scheme.universalHomeomorphism_reductionι :
    ∀ X : AlgebraicGeometry.Scheme.{u},
      AlgebraicGeometry.UniversalHomeomorphism (AlgebraicGeometry.Scheme.reductionι X))
