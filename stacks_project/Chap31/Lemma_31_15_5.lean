/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.SerreCondition
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.15.5: let `X` be a locally Noetherian scheme and let `D ⊆ X` be an effective
Cartier divisor. If `X` satisfies `(S_k)`, then `D` satisfies `(S_{k - 1})`. -/
@[stacks 0B3R] #check
  (AlgebraicGeometry.Scheme.satisfiesSerreConditionS_subscheme_pred_of_isEffectiveCartierDivisor :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      (D : X.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
      (k : ℕ),
      X.satisfiesSerreConditionS k →
        D.subscheme.satisfiesSerreConditionS (k - 1))
