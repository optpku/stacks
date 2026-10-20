/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Polynomial.LaurentUnits
import StacksCheckRecall

@[expose] public section

open scoped LaurentPolynomial

/- Exercise 111.64.3 (Units): the group of units of `ℤ[x, 1/x]` as an abelian group is
identified with `Additive ℤˣ × ℤ`. -/
@[stacks 0GRV] #check
  (LaurentPolynomial.intUnitsAddEquiv :
    Additive (ℤ[T;T⁻¹])ˣ ≃+ Additive ℤˣ × ℤ)
