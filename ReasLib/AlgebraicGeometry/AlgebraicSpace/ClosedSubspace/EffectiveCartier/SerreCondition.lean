module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SerreCondition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Serre conditions of effective Cartier divisors on locally Noetherian algebraic spaces

An effective Cartier divisor on a locally Noetherian algebraic space satisfying
`(S_k)` satisfies `(S_{k - 1})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `S` be a scheme and let `X` be a locally Noetherian algebraic
space over `S`. Let `D ⊂ X` be an effective Cartier divisor. If `X` is `(S_k)`, then
`D` is `(S_{k - 1})`. -/
@[stacks 0B4G]
theorem satisfiesSerreConditionS_pred_of_isEffectiveCartierDivisor
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] (k : ℕ)
    (hX : satisfiesSerreConditionS X k) :
    satisfiesSerreConditionS D.X (k - 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
