/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.QuotientLifting
import StacksCheckRecall

/-!
# Lemma 15.76.2 (0BCA)

@stack 0BCA
-/

@[expose] public section

/- Lemma 15.76.2: bounded-above term-class representatives lift across a quotient when
surjectivity lifts inside the class. -/
@[stacks 0BCA "Lemma 15.76.2"]
#check @CategoryTheory.DerivedCategory.QuotientLifting.exists_termsIn
