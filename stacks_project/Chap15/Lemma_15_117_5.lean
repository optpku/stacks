/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.WeakSolution.PurelyInseparableStep
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.117.5

The source-facing separable replacement theorem is owned by
`IsSolutionFor.exists_separable_of_purelyInseparable_prime`.  This chapter file is deliberately a
thin recall, so downstream files can import the ReasLib owner without inheriting chapter-local
monogenic rings, denominator choices, or temporary integral-closure instances.

@stack 0GLV
-/

/- Lemma 15.117.5: replace a prime purely inseparable solution step by a separable one. -/
@[stacks 0GLV "Lemma 15.117.5: separable replacement of a prime purely inseparable solution"]
#check @IsSolutionFor.exists_separable_of_purelyInseparable_prime

#check @IsSolutionFor
#check @IsSeparableSolutionFor

end
