/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Adic.Descent
import StacksCheckRecall

/-!
# Lemma 15.37.9 (07EH)

@stack 07EH
-/

@[expose] public section

/- Lemma 15.37.9 (07EH): adic formal smoothness descends after a base change that splits as a
map of modules. -/
@[stacks 07EH]
#check @RingHom.formally_smooth_for_adic_of_split_baseChange
