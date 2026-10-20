/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.PurelyInseparable
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.112.4

The source-facing purely inseparable ramification statement is owned by the reusable
`PurelyInseparable` extension leaf.  The repository path retains the legacy `15.112.4` name;
tag `09E6` is the current Stacks Lemma 15.113.4 entry.

@stack 09E6
-/

/- Lemma 15.112.4 (09E6; current Stacks Lemma 15.113.4): the ramification index is a power of
the residue characteristic in a purely inseparable fraction-field extension. -/
@[stacks 09E6 "purely inseparable ramification index"]
#check @ramificationIndex_eq_pow_of_isPurelyInseparable
