/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Model
import StacksCheckRecall

universe u

/- Definition 53.2.7: a nonsingular projective model of a curve `X` over `k` is a
regular projective curve together with a chosen isomorphism `k(X) ≅ k(Y)`. -/
@[stacks 0BY2] #check
  (AlgebraicGeometry.NonsingularProjectiveModel.WithIso :
    {k : Type u} → [Field k] →
      (X : AlgebraicGeometry.SchemeOverField k) →
        [AlgebraicGeometry.Curve X] → Type (u + 1))
