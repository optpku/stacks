/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.IndSmooth.FieldReduction
import StacksCheckRecall

@[expose] public section

/- Lemma 16.8.4: reduction of ind-smoothness to field sources is owned by
`RingHom.IndSmooth.of_field_cases`. -/
@[stacks 07F5]
#check @RingHom.IndSmooth.of_field_cases
