/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity

/-!
# Lemma 15.30.6

@stack 062I
-/

@[expose] public section

/- Lemma 15.30.6, tag `062I`: the module-valued `H1`-regular to
quasi-regular implication is owned by the shared sequence hierarchy. -/
@[stacks 062I "H1-regular sequences are quasi-regular"]
#check @RingTheory.Sequence.IsH1RegularOn.isQuasiRegular
