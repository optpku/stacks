/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Quotient
import StacksCheckRecall

/-!
# Lemma 15.79.5 (09AS)

@stack 09AS

The two-ideal perfectness criterion for derived quotient base changes is owned by ReasLib.
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.79.5 (09AS): perfectness modulo `I` and modulo `J` implies perfectness modulo
`I * J`. -/
@[stacks 09AS "Lemma 15.79.5"]
#check @isPerfect_derivedTensorWithAlgebra_quotient_mul_of_isPerfect_quotient_left_right
