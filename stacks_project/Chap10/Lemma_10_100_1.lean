/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Localization.Square
import StacksCheckRecall

/-!
# Lemma 10.100.1

@stack 00MQ

The four clauses are owned by the reusable localized-square API.  In
particular, the ascent clauses do not carry the local-ring hypotheses used
only for faithfully flat descent.
-/

@[expose] public section

@[stacks 00MQ "(1), module flatness ascent"]
#check @Module.Flat.LocalizationSquare.baseChange

@[stacks 00MQ "(2), module flatness descent"]
#check @Module.Flat.LocalizationSquare.descend

@[stacks 00MQ "(3), algebra flatness ascent"]
#check @RingHom.Flat.LocalizationSquare.baseChange

@[stacks 00MQ "(4), algebra flatness descent"]
#check @RingHom.Flat.LocalizationSquare.descend
