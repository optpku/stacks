/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.Hilbert
import StacksCheckRecall

@[expose] public section

/-! @stack 00K2 -/

/-!
# Example 10.58.9

The standard-graded multivariate-polynomial Hilbert theorem is owned by the reusable
`MvPolynomial` leaf.  This chapter entry is a direct recall, so later files can import the same
owner without depending on Chap10.
-/

/- API design: the owner keeps homogeneous pieces as `Submodule k M`, imports the shared
natural-to-integer action, and leaves K0/dimension comparison maps in ReasLib. -/

/- Example 10.58.9 (Tag 00K2): a finite graded module over the standard graded polynomial ring
`MvPolynomial (Fin d) k` has a numerical-polynomial Hilbert function `n ↦ Module.finrank k (ℳ n)`.
The recalled owner is generic in a finite variable type, with `Fin d` as this source instance. -/
@[stacks 00K2]
#check @MvPolynomial.finrank_isNumericalPolynomial
