/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap71.Lemma_71_8_1_SerreCondition

/-!
# Serre conditions of effective Cartier divisors on locally Noetherian algebraic spaces

An effective Cartier divisor on a locally Noetherian algebraic space satisfying
`(S_k)` satisfies `(S_{k - 1})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.8.1: Let `S` be a scheme and let `X` be a locally Noetherian algebraic
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
