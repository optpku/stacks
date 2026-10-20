/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity

/-!
# Lemma 15.30.3

@stack 0CEM
-/

@[expose] public section

/- Lemma 15.30.3 (Stacks Lemma 15.30.3 (1)), tag `0CEM`: the module-valued
Koszul-to-`H_1` bridge is owned by `ReasLib.RingTheory.Sequence.Koszul.Regularity`. -/
@[stacks 0CEM "Koszul-regular implies H1-regular"]
#check @RingTheory.Sequence.isH1RegularOn_of_isKoszulRegularOn

/- Lemma 15.30.3 (Stacks Lemma 15.30.3 (2)), tag `0CEM`: the ring-valued
Koszul-to-`H_1` bridge is owned by `ReasLib.RingTheory.Sequence.Koszul.Regularity`. -/
@[stacks 0CEM "Koszul-regular sequences are H1-regular"]
#check @RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence
