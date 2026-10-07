module

public import ReasLib.RingTheory.Module.Support.LinearMap
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.79.4

The three residue-fiber loci and their basic-open consequences are recalled
from the canonical `LinearMap` owner.

@stack 00O0
-/

-- Lemma 10.79.4 (1)-(3): injective residue fibers.
@[stacks 00O0 "(1)"]
#check @LinearMap.isOpen_fiberInjectiveLocus
@[stacks 00O0 "(2)"]
#check @LinearMap.injective_away_of_basicOpen_subset_fiberInjectiveLocus
@[stacks 00O0 "(3)"]
#check @LinearMap.coker_away_finite_projective_of_basicOpen_subset_fiberInjectiveLocus

-- Lemma 10.79.4 (4)-(6): surjective residue fibers.
@[stacks 00O0 "(4)"]
#check @LinearMap.isOpen_fiberSurjectiveLocus
@[stacks 00O0 "(5)"]
#check @LinearMap.surjective_away_of_basicOpen_subset_fiberSurjectiveLocus
@[stacks 00O0 "(6)"]
#check @LinearMap.ker_away_finite_projective_of_basicOpen_subset_fiberSurjectiveLocus

-- Lemma 10.79.4 (7)-(8): bijective residue fibers.
@[stacks 00O0 "(7)"]
#check @LinearMap.isOpen_fiberBijectiveLocus
@[stacks 00O0 "(8)"]
#check @LinearMap.bijective_away_of_basicOpen_subset_fiberBijectiveLocus

-- The source uses right-tensor models; these bridges identify them with the canonical loci.
@[stacks 00O0 "right-tensor injectivity view"]
#check @LinearMap.rTensor_injective_iff_mem_fiberInjectiveLocus
@[stacks 00O0 "right-tensor surjectivity view"]
#check @LinearMap.rTensor_surjective_iff_mem_fiberSurjectiveLocus
@[stacks 00O0 "right-tensor bijectivity view"]
#check @LinearMap.rTensor_bijective_iff_mem_fiberBijectiveLocus
