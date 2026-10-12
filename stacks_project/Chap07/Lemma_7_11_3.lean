/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.LocallySurjective

/-!
# Lemma 7.11.3

The reusable bridge from local surjectivity to the kernel-pair coequalizer is
owned by ReasLib. This chapter file retains the labeled source-facing recall.
-/

@[expose] public section

/- Lemma 7.11.3 (086K): a locally surjective map of set-valued sheaves is the
coequalizer of the two projections from its kernel pair. -/
@[stacks 086K] #check @CategoryTheory.Sheaf.IsLocallySurjective.isColimitCofork

#check @CategoryTheory.Sheaf.IsLocallySurjective.effectiveEpi
