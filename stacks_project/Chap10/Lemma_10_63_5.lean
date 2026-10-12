/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.AssociatedPrime.Finiteness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.63.5

@stack 00LC
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.63.5 (Tag 00LC): if `R` is a Noetherian ring and `M` is a finite `R`-module, then
the exact-annihilator associated-prime set is finite. -/
@[stacks 00LC]
#check @associatedPrimesOfModule.finite
