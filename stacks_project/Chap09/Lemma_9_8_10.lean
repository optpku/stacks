/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.IntermediateField.Algebraic
import StacksCheckRecall

@[expose] public section

/- Lemma 9.8.10 (Tag 0BID): a subring of an algebraic field extension that contains the base
field is a field. -/
@[stacks 0BID]
#check Subring.isFieldOfAlgebraic
