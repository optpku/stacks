/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Relative.QuasiFinite
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.125.5

@stack 00QG

The reusable polynomial-algebra dimension bound is owned by ReasLib.
-/

@[stacks 00QG]
#check @Algebra.QuasiFinite.ringKrullDim_le_of_mvPolynomial
