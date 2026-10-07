module

public import ReasLib.Topology.Sober.GenericPoint
import StacksCheckRecall

@[expose] public section

/-!
# Definition 5.8.6

Generic-point and sober-space statements are owned by
`ReasLib.Topology.Sober.GenericPoint`.
-/

/- Definition 5.8.6 (1): generic points are the canonical Mathlib predicate. -/
@[stacks 004X "generic points of irreducible closed subsets"]
#check @IsGenericPoint

/- Definition 5.8.6 (1): the irreducible-closed specialization has a reusable specification. -/
@[stacks 004X "generic points of irreducible closed subsets"]
#check @IrreducibleCloseds.isGenericPoint_iff_mem_and_eq_closure_singleton

/- Definition 5.8.6 (2): Kolmogorov spaces are the canonical Mathlib predicate. -/
@[stacks 004X "Kolmogorov spaces"]
#check @T0Space

/- Definition 5.8.6 (3): quasi-sober spaces are the canonical Mathlib predicate. -/
@[stacks 004X "quasi-sober spaces"]
#check @QuasiSober

/- Definition 5.8.6 (4): sober spaces are represented by `T0Space` and `QuasiSober`. -/
@[stacks 004X "sober spaces via unique generic points"]
#check @sober_iff_forall_irreducibleCloseds_existsUnique_genericPoint
