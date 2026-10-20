/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Locus.BaseChange

@[expose] public section

/-!
# Smooth Locus Flat Base-Change Recall

@stack 00TG

The reusable owner is `Algebra.smoothLocus`.  Its flat base-change equality is
independent of the chapter's cotangent-homology and localization proof
plumbing.
-/

/- Lemma 10.137.17, tag 00TG: for a finitely presented map `R → S` and a
flat base change `R → R'`, the smooth locus of `R' → R' ⊗[R] S` is the inverse
image of the smooth locus of `R → S`. -/
@[stacks 00TG "flat base change of smooth loci"]
#check @Algebra.smoothLocus_preimage_includeRight_eq_baseChange

@[stacks 00TG "pointwise smooth-locus base change"]
#check @Algebra.mem_smoothLocus_baseChange_iff
