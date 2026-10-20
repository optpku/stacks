/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.Polynomial
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.134.3

@stack 08Q1

The source statement is the polynomial-algebra specialization of the shared
presentation-isomorphism API.
-/

open scoped NaiveCotangent

/- Lemma 10.134.3 [stacks 08Q1]: if `MvPolynomial ι A ≃ₐ[A] B`, then the canonical naive
cotangent complex `NL{B⁄A}` is homotopy equivalent to the single complex on `Ω[B⁄A]` in degree
zero.  The reusable owner accepts an arbitrary algebra equivalence rather than a chapter-local
presentation construction. -/
@[stacks 08Q1]
#check @Algebra.NaiveCotangent.Polynomial.homotopyEquivSingleZero

#check @Algebra.Extension.NaiveCotangent.Bijective.homotopyEquivSingleZero
