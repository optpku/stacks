/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.QuotientLift.Cover

@[expose] public section

/-!
@stack 04B1
-/

/-!
# Standard-Smooth Lifts of Smooth Quotient Algebras Recall

The reusable API separates a single standard-smooth chart lift from the
standard-open cover supplied by a smooth quotient algebra.  Its proof owns all
presentation, Jacobian, and scalar-tower choices internally.
-/

/- Lemma 10.137.19, tag 04B1: a smooth algebra over `R ⧸ I` has a
standard-open cover whose charts are reductions of standard-smooth
`R`-algebras. -/
@[stacks 04B1 "standard-smooth lift cover of a smooth quotient algebra"]
#check @Algebra.Smooth.QuotientLift.exists_standardCover_of_quotient

#check @Algebra.IsStandardSmooth.exists_lift_of_quotient
