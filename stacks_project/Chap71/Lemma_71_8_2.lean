module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_25_4_Normal
public import stacks_project.Chap71.Definition_71_6_1_EffectiveCartier
public import stacks_project.Chap71.Lemma_71_8_1_SerreCondition

/-!
# Effective Cartier divisors on normal locally Noetherian algebraic spaces

An effective Cartier divisor on a locally Noetherian normal algebraic space
satisfies Serre's condition `(S₁)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.8.2: Let `S` be a scheme and let `X` be a locally Noetherian normal
algebraic space over `S`. Let `D ⊂ X` be an effective Cartier divisor. Then `D`
is `(S₁)`. -/
@[stacks 0B4H]
theorem IsEffectiveCartierDivisor.satisfiesSerreConditionS_one
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X] [IsNormal X]
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    satisfiesSerreConditionS D.X 1 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
