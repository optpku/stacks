/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Module.Support.LinearMap
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.79.1

@stack 05GE

The reusable owner is `LinearMap.surjectiveLocus`; the three source clauses
are recalled through its finite-target and forward-direction companions.
-/

/- Lemma 10.79.1 (1): for a map with finite target, the localized and
residue-field fiber surjectivity loci agree. -/
@[stacks 05GE "(1)"]
#check @LinearMap.surjectiveLocus_eq_fiberSurjectiveLocus_of_finite

/- Lemma 10.79.1 (2): the localized surjectivity locus is open. -/
@[stacks 05GE "(2)"]
#check @LinearMap.isOpen_surjectiveLocus_of_finite

/- Lemma 10.79.1 (3): a basic-open inclusion in the surjectivity locus
implies surjectivity of the corresponding away-localized map. -/
@[stacks 05GE "(3)"]
#check @LinearMap.surjective_away_of_basicOpen_subset_surjectiveLocus

/- Canonical support descriptions and the bidirectional local-to-away criterion. -/
#check @LinearMap.baseChange_surjective_iff_rTensor_surjective
#check @LinearMap.surjectiveLocus_eq_compl_support_coker
#check @LinearMap.fiberSurjectiveLocus_eq_compl_support_coker
#check @LinearMap.basicOpen_subset_surjectiveLocus_iff
