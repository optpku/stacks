/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.FiniteColength
import StacksCheckRecall

/-!
# Lemma 10.59.9

@stack 00KB
-/

@[expose] public section

/- Lemma 10.59.9 (Stacks 00KB): replacing an infinite-length finite module
by a finite-colength submodule changes its eventual Hilbert--Samuel
`χ`-polynomial only in lower degree. -/
@[stacks 00KB]
#check @Ideal.HilbertSamuel.chiPolynomial_sub_degree_lt

@[stacks 00KB "positive Hilbert-Samuel degree"]
#check @Ideal.HilbertSamuel.chiPolynomial_degree_pos

@[stacks 00KB "finite-colength Hilbert-Samuel degree"]
#check @Ideal.HilbertSamuel.chiPolynomial_degree_eq_of_finiteColength
