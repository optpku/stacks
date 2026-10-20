module

public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.19.2 (1) is recalled canonically by `IsClosed.stableUnderSpecialization`: any closed
subset of a topological space is stable under specialization. -/
@[stacks 0062 "closed subsets are stable under specialization"]
#check IsClosed.stableUnderSpecialization

/- Lemma 5.19.2 (2) is recalled canonically by `IsOpen.stableUnderGeneralization`: any open
subset of a topological space is stable under generalization. -/
@[stacks 0062 "open subsets are stable under generalization"]
#check IsOpen.stableUnderGeneralization

/- Lemma 5.19.2 (3): a subset is stable under specialization if and only if its complement is
stable under generalization. This is recalled exactly by the canonical complement theorem
`stableUnderGeneralization_compl_iff`. -/
@[stacks 0062 "specialization stability is complement-dual to generalization stability"]
#check stableUnderGeneralization_compl_iff
