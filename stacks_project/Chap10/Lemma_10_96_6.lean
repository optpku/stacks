/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.Jacobson
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.96.6
@stack 05GI
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.96.6 (1): an element of the `I`-adic completion whose image in `R ⧸ I` is a unit is
already a unit in the completion. -/
@[stacks 05GI "(1), unit detection"]
#check @AdicCompletion.isUnit_of_isUnit_evalOne

/- Lemma 10.96.6 (5): the kernel of the canonical projection `R^∧ → R ⧸ I` is contained in the
Jacobson radical of the `I`-adic completion. -/
@[stacks 05GI "(5), first-quotient kernel"]
#check @AdicCompletion.ker_evalOne_le_jacobson

/- Lemma 10.96.6 (4): the extended ideal `I R^∧` is contained in the Jacobson radical of the
`I`-adic completion. -/
@[stacks 05GI "(4), extended ideal"]
#check @AdicCompletion.idealMap_le_jacobson

/- Lemma 10.96.6 (3): every element of the `I`-adic completion congruent to `1` modulo the
extended ideal `I R^∧` is a unit. -/
@[stacks 05GI "(3), unit modulo the extended ideal"]
#check @AdicCompletion.isUnit_of_sub_one_mem_idealMap

/- Lemma 10.96.6 (2): an element of `R` congruent to `1` modulo `I` maps to a unit in the
`I`-adic completion. -/
@[stacks 05GI "(2), base element maps to a unit"]
#check @AdicCompletion.isUnit_algebraMap_of_sub_one_mem

@[stacks 05GI "unit detection in the first quotient"]
#check @AdicCompletion.evalOneₐ_surjective

@[stacks 05GI "Jacobson radical unit criterion"]
#check @Ideal.isUnit_of_sub_one_mem_jacobson_bot
