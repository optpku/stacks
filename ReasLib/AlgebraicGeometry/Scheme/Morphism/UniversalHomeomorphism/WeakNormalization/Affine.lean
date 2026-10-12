/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.WeakNormalization.Normal

/-!
# Affine weak normality

This module characterizes weak normality of an affine spectrum in ring-theoretic terms.
-/

@[expose] public section

open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable (A : Type u) [CommRing A]

/-- An affine spectrum with finitely many irreducible components is weakly normal exactly when
its ring is seminormal and satisfies prime divisibility by nonzerodivisors. -/
@[stacks 0H3T]
theorem weaklyNormal_Spec_iff_seminormalRing_and_primeDivisibility
    [Finite (irreducibleComponents (Spec (CommRingCat.of A)))] :
    Scheme.WeaklyNormal (Spec (CommRingCat.of A)) ↔
      SeminormalRing A ∧
        ∀ p : ℕ, Nat.Prime p →
          ∀ z w : A,
            z ∈ nonZeroDivisors A →
            z ^ p ∣ w ^ p →
            z ∣ (p : A) * w →
            z ∣ w := sorry

end AlgebraicGeometry
