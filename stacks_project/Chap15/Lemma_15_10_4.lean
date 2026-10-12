/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.Polynomial
import StacksCheckRecall

/-!
# Lemma 15.10.4

@stack 0EM0
-/

@[expose] public section

open Polynomial

universe u v w w'

namespace Algebra

variable {A : Type u} {B : Type v} {B₁ : Type w} {B₂ : Type w'}
variable [CommRing A] [CommRing B] [CommRing B₁] [CommRing B₂]
variable [Algebra A B] [Module.Finite A B]
variable (I : Ideal A)
variable [Algebra (A ⧸ I) B₁] [Algebra (A ⧸ I) B₂]

-- Lemma 15.10.4 (0EM0): a distinguished closed-fiber product component supplies a monic
-- polynomial relation with reduction `(X - 1) * X ^ d`.
@[stacks 0EM0]
#check
  (exists_monic_polynomial_of_product_decomposition_mod_ideal (I := I) :
    I ≤ Ring.jacobson A →
      (hprod : (B ⧸ Ideal.map (algebraMap A B) I) ≃ₐ[A ⧸ I] (B₁ × B₂)) →
      Function.Surjective (algebraMap (A ⧸ I) B₁) →
      (b : B) →
      hprod (Ideal.Quotient.mk (Ideal.map (algebraMap A B) I) b) =
          ((1 : B₁), (0 : B₂)) →
        ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
          f.Monic ∧ aeval b f = 0 ∧
            f.map (Ideal.Quotient.mk I) = ((X - 1) * X ^ d : (A ⧸ I)[X]))

end Algebra
