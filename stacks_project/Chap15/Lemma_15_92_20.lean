/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Nakayama.Derived
import StacksCheckRecall

/-!
# Lemma 15.92.20: derived Nakayama

The reusable owner contains the source-facing vanishing criterion. Generator selection,
powered-Koszul vanishing, and shift bookkeeping remain proof concerns rather than chapter API.

@stack 0G1U
-/

@[expose] public section

/- Lemma 15.92.20 (0G1U): a derived-complete object whose derived reduction modulo a finitely
generated ideal is zero is itself zero. -/
@[stacks 0G1U "Lemma 15.92.20"]
#check @DerivedCategory.DerivedComplete.isZero_of_derivedTensor_quotient_isZero
