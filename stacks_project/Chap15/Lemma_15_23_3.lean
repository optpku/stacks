/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Reflexive
import StacksCheckRecall

/-!
# Lemma 15.23.3

The source is the discrete-valuation-ring specialization of the canonical evaluation-surjectivity
owner.

@stack 0B36
-/

@[expose] public section

/- Lemma 15.23.3: over a discrete valuation ring, the double-dual evaluation map of a finite
module is surjective. -/
@[stacks 0B36 "Lemma 15.23.3"]
#check @Module.Dual.eval_surjective_of_isDiscreteValuationRing

/- The reusable principal-ideal-domain generalization of Lemma 15.23.3. -/
#check @Module.Dual.eval_surjective_of_isPrincipalIdealRing
