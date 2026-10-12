/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.PolynomialFactorization

@[expose] public section

/-!
# Lemma 15.9.5 (0ALH)

@stack 0ALH
-/

-- Lemma 15.9.5: a monic coprime factorization modulo an ideal lifts etale-locally while the
-- quotient remains unchanged.
@[stacks 0ALH "Lemma 15.9.5"]
#check @Algebra.exists_etale_lift_factorization_of_monic_mod_ideal
