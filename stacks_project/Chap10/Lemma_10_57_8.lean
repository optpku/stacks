/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
import StacksCheckRecall

@[expose] public section

/-!
# Homogeneity of minimal primes in graded rings

@stack 00JU
-/

/- Lemma 10.57.8 (1): every minimal prime of an `ℕ`-graded commutative ring
is homogeneous. -/
@[stacks 00JU "(1)"]
#check @Ideal.isHomogeneous_of_mem_minimalPrimes

/- Lemma 10.57.8 (2): if `I` is a homogeneous ideal of an `ℕ`-graded commutative ring `S`, then
every minimal prime ideal over `I` is homogeneous. -/
@[stacks 00JU "(2)"]
#check @Ideal.IsHomogeneous.minimalPrime
