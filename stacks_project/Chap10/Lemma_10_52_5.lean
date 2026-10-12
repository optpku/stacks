/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Length.RestrictScalars
import StacksCheckRecall

@[expose] public section

/-!
# Length under restriction of scalars

@stack 00IX

Lemma 10.52.5 is split into the canonical length inequality and the equality for a surjective
scalar map. The first is owned by ReasLib; the second is already owned by Mathlib.
-/

/- Lemma 10.52.5 (1): restriction of scalars cannot decrease module length. -/
@[stacks 00IX "(1), length inequality"]
#check @Module.length_le_restrictScalars

/- Lemma 10.52.5 (2): a surjective scalar map preserves module length. -/
@[stacks 00IX "(2), equality for a surjective scalar map"]
#check @Module.length_eq_of_surjective
