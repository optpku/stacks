/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Exact
import StacksCheckRecall

/-!
# Hilbert--Samuel invariants in a short exact sequence

@stack 00KC
-/

@[expose] public section

/- Lemma 10.59.10 (1): the error in additivity of eventual
Hilbert--Samuel `χ`-polynomials across a short exact sequence has lower
degree. -/
@[stacks 00KC "(1)"]
#check @Ideal.HilbertSamuel.ShortExact.chi_error_degree_lt

/- Lemma 10.59.10 (2): the degree of the middle eventual
Hilbert--Samuel `χ`-polynomial is the maximum of the endpoint degrees. -/
@[stacks 00KC "(2)"]
#check @Ideal.HilbertSamuel.ShortExact.chi_degree_eq_max

/- Lemma 10.59.10 (3): the Hilbert--Samuel degree invariant is
max-additive on a short exact sequence; it is recalled from the neutral
shared owner. -/
@[stacks 00KC "(3)"]
#check @Ideal.HilbertSamuel.ShortExact.degree_eq_max
