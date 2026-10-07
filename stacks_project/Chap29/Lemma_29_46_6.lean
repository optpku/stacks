module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subring

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.46.6: if `A ⊂ B` is a ring extension such that `Spec(B) → Spec(A)` is a universal
homeomorphism and `A ≠ B`, then either some `b ∈ B \ A` has `b ^ 2 ∈ A` and `b ^ 3 ∈ A`, or for
some prime number `p` some `b ∈ B \ A` has `p * b ∈ A` and `b ^ p ∈ A`. -/
@[stacks 0CNC] #check
  (AlgebraicGeometry.UniversalHomeomorphism.exists_not_mem_sq_cube_or_prime_mul_power_mem :
    ∀ {B : Type u} [CommRing B] (A : Subring B),
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)) →
        A ≠ ⊤ →
          (∃ b : B, b ∉ A ∧ b ^ 2 ∈ A ∧ b ^ 3 ∈ A) ∨
            ∃ (p : ℕ) (b : B), Nat.Prime p ∧ b ∉ A ∧ (p : B) * b ∈ A ∧ b ^ p ∈ A)
