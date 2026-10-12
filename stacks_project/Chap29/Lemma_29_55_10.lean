/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Affine

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

/- Lemma 29.55.10: let `X = Spec(A)` be an affine scheme with finitely many irreducible
components. Then `X` is weakly normal if and only if `A` is seminormal and, for every prime
number `p` and `z, w : A`, if `z` is a nonzerodivisor, `w^p` is divisible by `z^p`, and
`p * w` is divisible by `z`, then `w` is divisible by `z`. -/
@[stacks 0H3T] #check
  (AlgebraicGeometry.weaklyNormal_Spec_iff_seminormalRing_and_primeDivisibility :
    ∀ (A : Type u) [CommRing A]
      [Finite (irreducibleComponents (Spec (CommRingCat.of A)))],
      Scheme.WeaklyNormal (Spec (CommRingCat.of A)) ↔
        SeminormalRing A ∧
          ∀ p : ℕ, Nat.Prime p →
            ∀ z w : A,
              z ∈ nonZeroDivisors A →
              z ^ p ∣ w ^ p →
              z ∣ (p : A) * w →
              z ∣ w)
