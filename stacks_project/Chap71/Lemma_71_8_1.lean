module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.EffectiveCartier.SerreCondition
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.8.1: Let `S` be a scheme and let `X` be a locally Noetherian algebraic
space over `S`. Let `D ⊂ X` be an effective Cartier divisor. If `X` is `(S_k)`, then
`D` is `(S_{k - 1})`. -/
@[stacks 0B4G] #check
  (AlgebraicGeometry.AlgebraicSpace.satisfiesSerreConditionS_pred_of_isEffectiveCartierDivisor :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
      (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] (k : ℕ)
      (hX : satisfiesSerreConditionS X k),
      satisfiesSerreConditionS D.X (k - 1))

end AlgebraicGeometry.AlgebraicSpace
