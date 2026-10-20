/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity.BaseChange

/-!
# Koszul regularity under flat base change

@stack 062H
-/

@[expose] public section

/- Lemma 15.30.5 (1): flat scalar extension preserves module-valued `H₁`-regularity. -/
@[stacks 062H "Lemma 15.30.5 (1)"]
#check @RingTheory.Sequence.IsH1RegularOn.of_flat

/- Lemma 15.30.5 (2): flat scalar extension preserves module-valued Koszul-regularity. -/
@[stacks 062H "Lemma 15.30.5 (2)"]
#check @RingTheory.Sequence.IsKoszulRegularOn.of_flat

#check @RingTheory.Sequence.IsH1RegularOn.of_flat_of_isBaseChange
#check @RingTheory.Sequence.IsKoszulRegularOn.of_flat_of_isBaseChange
