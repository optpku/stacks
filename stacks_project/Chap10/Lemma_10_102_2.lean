/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.SplitUnit
import StacksCheckRecall

/-!
# Splitting a unit entry from a finite free complex

@stack 00MT
-/

/- Lemma 10.102.2: a unit differential entry splits an identity disk from a
bounded finite free complex. -/
@[stacks 00MT]
#check @FiniteFreeComplex.exists_iso_biprod_identityDisk_of_isUnit_diffEntry
