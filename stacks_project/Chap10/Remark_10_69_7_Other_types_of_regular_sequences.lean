/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity

/-!
# Remark 10.69.7

@stack 061T
-/

@[expose] public section

/- Remark 10.69.7 (1), tag `061T`: Koszul-regular sequences. -/
@[stacks 061T "Koszul-regular sequences"]
#check @RingTheory.Sequence.IsKoszulRegularSequence

/- Remark 10.69.7 (2), tag `061T`: `H1`-regular sequences. -/
@[stacks 061T "H1-regular sequences"]
#check @RingTheory.Sequence.IsH1RegularSequence

/- Remark 10.69.7 (3), tag `061T`: regular sequences are
Koszul-regular. -/
@[stacks 061T "regular sequences are Koszul-regular"]
#check @RingTheory.Sequence.IsRegular.isKoszulRegularOn

/- Remark 10.69.7 (4), tag `061T`: Koszul-regular sequences are
`H1`-regular. -/
@[stacks 061T "Koszul-regular sequences are H1-regular"]
#check @RingTheory.Sequence.isH1RegularSequence_of_isKoszulRegularSequence

/- Remark 10.69.7 (5), tag `061T`: `H1`-regular sequences are
quasi-regular. -/
@[stacks 061T "H1-regular sequences are quasi-regular"]
#check @RingTheory.Sequence.isQuasiRegularSequence_of_isH1RegularSequence
