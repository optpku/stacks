/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.ReesAlgebra.Integral
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial equations for idempotents modulo extended ideals

@stack 09XG

An element of an integral algebra which is idempotent modulo an extended ideal satisfies a
monic polynomial whose reduction is a product of equal powers of `X` and `X - 1`.
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B]

/-- Lemma 15.9.9 (Stacks `09XG`): if `b : B` is idempotent modulo the extension of `I`,
then `b` satisfies a monic polynomial whose reduction modulo `I` is
`X ^ d * (X - 1) ^ d` for some positive `d`. -/
@[stacks 09XG]
theorem exists_monic_polynomial_of_isIdempotentElem_mod_map
    (I : Ideal A) (b : B)
    (hb :
      IsIdempotentElem
        (Ideal.Quotient.mk (I.map (algebraMap A B)) b : B ⧸ I.map (algebraMap A B))) :
    ∃ d : ℕ, 0 < d ∧ ∃ f : A[X],
      f.Monic ∧ aeval b f = 0 ∧
        f.map (Ideal.Quotient.mk I) = (X ^ d * (X - 1) ^ d : (A ⧸ I)[X]) := sorry

end Algebra
