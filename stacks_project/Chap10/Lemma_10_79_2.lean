/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Module.Support.LinearMap
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.79.2

The local bijectivity locus and its support description are recalled from the
canonical `LinearMap` owner.

@stack 05GF
-/

-- Lemma 10.79.2: the local bijectivity locus is open for a map from a finite module to a
-- finitely presented module.
@[stacks 05GF]
#check @LinearMap.isOpen_bijectiveLocus

@[stacks 05GF "kernel-support criterion"]
#check @LinearMap.injectiveAt_iff_notMem_support_ker

@[stacks 05GF "kernel-and-cokernel support criterion"]
#check @LinearMap.bijectiveAt_iff_notMem_support_ker_and_coker

@[stacks 05GF "basic-open localization criterion"]
#check @LinearMap.basicOpen_subset_bijectiveLocus_of_bijective_away
