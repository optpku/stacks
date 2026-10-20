/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Degree
import StacksCheckRecall

/-!
# Lemma 10.59.7

@stack 00K9
-/

@[expose] public section

/- Lemma 10.59.7 (1), Stacks 00K9: the degree of an eventual
Hilbert--Samuel `φ`-polynomial is independent of the ideal of definition. -/
@[stacks 00K9 "(1)"]
#check @Ideal.HilbertSamuel.phiPolynomial_degree_eq

/- Lemma 10.59.7 (2), Stacks 00K9: the degree of an eventual
Hilbert--Samuel `χ`-polynomial is independent of the ideal of definition. -/
@[stacks 00K9 "(2)"]
#check @Ideal.HilbertSamuel.chiPolynomial_degree_eq
