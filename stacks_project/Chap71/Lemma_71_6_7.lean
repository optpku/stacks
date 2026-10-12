/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_6_7_Instances
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 71.6.7
The sum of two effective Cartier divisors is an effective Cartier divisor.
-/
@[stacks 083V] #check
  (instIsEffectiveCartierDivisor_sum :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (D₁ D₂ : ClosedSubspace X)
      [IsEffectiveCartierDivisor D₁.ι] [IsEffectiveCartierDivisor D₂.ι],
      IsEffectiveCartierDivisor (effectiveCartierDivisorSum D₁ D₂).ι)

#check isEffectiveCartierDivisor_sum

#check isEffectiveCartierDivisor_mul
