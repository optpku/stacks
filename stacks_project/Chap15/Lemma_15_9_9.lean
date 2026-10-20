/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Integral.Idempotent
import StacksCheckRecall

/-!
# Lemma 15.9.9

@stack 09XG
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

-- Lemma 15.9.9 (09XG): an integral element which is idempotent modulo an extended ideal
-- satisfies a monic equation reducing to equal powers of `X` and `X - 1`.
@[stacks 09XG]
#check
  (exists_monic_polynomial_of_isIdempotentElem_mod_map :
    (I : Ideal A) → (b : B) →
      IsIdempotentElem
          (Ideal.Quotient.mk (I.map (algebraMap A B)) b : B ⧸ I.map (algebraMap A B)) →
        ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
          f.Monic ∧ aeval b f = 0 ∧
            f.map (Ideal.Quotient.mk I) = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]))

end Algebra
