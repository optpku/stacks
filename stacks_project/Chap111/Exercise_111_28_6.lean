/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.AssociatedGraded.NonZeroDivisors

@[expose] public section

universe u

open IsLocalRing Ideal.AssociatedGraded

namespace Ideal.AssociatedGraded

/- Exercise 111.28.6 (1): a nonzerodivisor initial class in the associated
graded ring lifts to a nonzerodivisor in the filtered local ring. -/
@[stacks 02EK]
#check
  (Ideal.AssociatedGraded.mem_nonZeroDivisors_of_stageClass :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {d : ℕ} {x : A},
      (hx : x ∈ stage (maximalIdeal A) A d) →
        stageClass (maximalIdeal A) d ⟨x, hx⟩ ∈
            nonZeroDivisors (ring (maximalIdeal A)) →
          x ∈ nonZeroDivisors A)

/- Exercise 111.28.6 (2): with a nonzerodivisor in the maximal ideal,
eventual injectivity on associated graded pieces also lifts nonzerodivisors. -/
@[stacks 02EK]
#check
  (Ideal.AssociatedGraded.mem_nonZeroDivisors_of_pieceMul_injective_eventually :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {d : ℕ} {x : A},
      (hx : x ∈ stage (maximalIdeal A) A d) →
        (∃ y ∈ maximalIdeal A, y ∈ nonZeroDivisors A) →
          (∃ N, ∀ n ≥ N, Function.Injective
            (pieceMul (maximalIdeal A) d n
              (Submodule.Quotient.mk
                ⟨x, hx⟩))) →
            x ∈ nonZeroDivisors A)

end Ideal.AssociatedGraded
