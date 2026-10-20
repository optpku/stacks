/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Pure.Topology
import StacksCheckRecall

/-!
# Pure Ideals and Closed Generalization-Stable Subsets

@stack 04PU
-/

@[expose] public section

/- Lemma 10.108.4 (04PU): pure ideals are detected by their zero loci among
closed subsets stable under generalization. The reusable API is directional:
well-definedness, existence, and the existing pure-ideal zero-locus
injectivity theorem replace a bespoke subtype bijection. -/
@[stacks 04PU]
#check @Ideal.Pure.zeroLocus_stableUnderGeneralization

@[stacks 04PU "pure zero-locus existence"]
#check @Ideal.Pure.exists_zeroLocus_eq_of_isClosed_of_stableUnderGeneralization

@[stacks 04PU "pure zero-locus injectivity"]
#check @Ideal.zeroLocus_inj_of_pure
