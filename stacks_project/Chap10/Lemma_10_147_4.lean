/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.IntegralClosure
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w
variable (R : Type u) (S : Type v) (B : Type w)
variable [CommRing R] [CommRing S] [CommRing B]
variable [Algebra R S] [Algebra R B] [Algebra.Smooth R S]

/- Lemma 10.147.4: the canonical smooth-base-change map on integral closures is bijective.
The map sends s ⊗ a to the same tensor with the integral element included in B. -/
@[stacks 03GG "integral closure commutes with smooth base change"] #check
  (TensorProduct.toIntegralClosure_bijective_of_smooth (R := R) (S := S) (B := B) :
    Function.Bijective
      (TensorProduct.toIntegralClosure R S B :
        S ⊗[R] integralClosure R B →ₐ[S] integralClosure S (S ⊗[R] B)))
