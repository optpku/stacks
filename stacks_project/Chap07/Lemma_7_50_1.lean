/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Sheafification.Sieve

/-!
# Lemma 7.50.1

The covering-sieve criterion is a reusable sheafification API, so this source
file records the Stacks label without reimplementing its universe-lift proof.
-/

@[expose] public section

/- Lemma 7.50.1 (00ZO): a sieve is covering if and only if its canonical inclusion into the
representable presheaf is a weak equivalence after sheafification. -/
@[stacks 00ZO] #check @CategoryTheory.Sieve.mem_iff_W_functorInclusion
