/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.38.5
@stack 00H6
-/

/- Lemma 10.38.5 (1).  The canonical owner accepts arbitrary monic polynomials, so it directly
subsumes the source's displayed coefficient presentation. -/
@[stacks 00H6 "(1), integrality of divisor coefficients"]
#check @Polynomial.isIntegral_coeff_of_dvd

/- Lemma 10.38.5 (2).  The owner records the corresponding radical membership coefficient by
coefficient, again without fixing a presentation by `Fin`-indexed tuples. -/
@[stacks 00H6 "(2), radical membership of divisor coefficients"]
#check @Polynomial.coeff_mem_radical_span_coeff_of_dvd
