/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Regular.BaseChange
import StacksCheckRecall

/-!
Lemma 15.41.3 (07C1): essentially finite type base change preserves regular ring maps.
The reusable owner is `RingHom.Regular.baseChange_of_essFiniteType`.
@stack 07C1
-/

@[expose] public section

/- Lemma 15.41.3 (Regular maps and base change): essentially finite type base
change preserves regular ring maps. -/
@[stacks 07C1] #check @RingHom.Regular.baseChange_of_essFiniteType
