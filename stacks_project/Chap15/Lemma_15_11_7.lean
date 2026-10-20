/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.ZeroLocus
import StacksCheckRecall

/-!
# Henselianity and zero loci

The radical-invariance theorem for henselian pairs is owned by `ReasLib`; this chapter file keeps
only the labeled source recall.

@stack 09XJ
-/

@[expose] public section

/- Lemma 15.11.7: equal closed subsets `V(I) = V(J)` give equivalent henselian-pair structures. -/
@[stacks 09XJ]
#check @henselianRing_iff_of_zeroLocus_eq
