/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.CoefficientField
import StacksCheckRecall

/-!
# Lemma 15.38.3

@stack 0C34
-/

@[expose] public section

/- Lemma 15.38.3, tag `0C34`: a separable residue-field extension of a complete local
`k`-algebra lifts to a coefficient-field section. -/
@[stacks 0C34]
#check @exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver
