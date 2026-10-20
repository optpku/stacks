/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Module.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 10.127.6

The three direct-limit descent statements for finitely presented modules are
owned by `Ring.DirectLimit.Module.FinitePresentation`.  This source entry
retains its Stacks label and checks the complete shared declarations without
installing a chapter-level stage algebra instance.

@stack 05N7
-/

@[expose] public section

/- Lemma 10.127.6 (1), Stacks tag `05N7`: a finitely presented module over a
direct limit descends to one stage. -/
@[stacks 05N7] #check @Ring.DirectLimit.Module.FinitePresentation.exists_stage

/- Lemma 10.127.6 (2), Stacks tag `05N7`: a map from the base change of a
finitely presented stage module descends after passing to a later stage. -/
@[stacks 05N7] #check @Ring.DirectLimit.Module.FinitePresentation.exists_stageMap

/- Lemma 10.127.6 (3), Stacks tag `05N7`: equality of base-changed maps out of
a finitely presented stage module is witnessed after passing to a later stage. -/
@[stacks 05N7] #check @Ring.DirectLimit.Module.FinitePresentation.exists_stage_eq
