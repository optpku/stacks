/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Graded
import StacksCheckRecall

/-!
# Lemma 10.98.3

@stack 0EKC
-/

@[expose] public section

/- Lemma 10.98.3 (0EKC): a surjective positive inverse system of finite
graded modules with successive ideal-power kernels has a finite graded quotient
realization.  The realization records the actual module, grading, quotient
equivalences, homogeneous-piece criterion, and successor squares. -/
@[stacks 0EKC]
#check @AdicCompletion.Graded.Realization.nonempty

@[stacks 0EKC "graded realization data"]
#check @AdicCompletion.Graded.Realization

@[stacks 0EKC "explicit graded realization constructor"]
#check @AdicCompletion.Graded.Realization.of

@[stacks 0EKC "graded quotient-system presentation"]
#check @AdicCompletion.QuotientSystem.Presentation
