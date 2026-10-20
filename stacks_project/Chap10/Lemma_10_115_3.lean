/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Quotient
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.115.3

@stack 00OX

The canonical owner proves the source statement from `I ≠ ⊥`; it does not
need the chapter wrapper's redundant properness hypothesis.
-/

@[stacks 00OX "finite normalization of a polynomial quotient"]
#check @MvPolynomial.NoetherNormalization.exists_finite_quotient_generators
