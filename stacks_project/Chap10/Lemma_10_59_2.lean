/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Ideal.HilbertSamuel.Finiteness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.59.2

@stack 00K5
-/

/- Lemma 10.59.2 (Stacks 00K5): the Hilbert--Samuel `χ`-function of a
finite-colength submodule gives eventual upper and shifted lower bounds for
the ambient module. -/
@[stacks 00K5]
#check @Ideal.HilbertSamuel.exists_eventually_chi_bounds
