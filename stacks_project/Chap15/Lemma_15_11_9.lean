/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.PairQuotient
import StacksCheckRecall

/-!
# Lemma 15.11.9

@stack 0DYD
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A]
variable (I J : Ideal A) (hIJ : I ≤ J)

-- Lemma 15.11.9 (0DYD): henselianity of `(A, J)` decomposes into henselianity of
-- `(A, I)` and of the quotient pair `(A ⧸ I, J / I)`.
@[stacks 0DYD]
#check
  (henselianRing_iff_henselianRing_and_quotient_henselianRing I J hIJ :
    HenselianRing A J ↔
      HenselianRing A I ∧
        HenselianRing (A ⧸ I) (J.map (Ideal.Quotient.mk I)))
