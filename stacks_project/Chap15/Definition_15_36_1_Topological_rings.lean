module

public import ReasLib.RingTheory.Topology.Adic.Complete
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import StacksCheckRecall

/-!
# Definition 15.36.1 (Topological rings) (07E8)

@stack 07E8
-/

@[expose] public section

/- Definition 15.36.1 (1), tag `07E8`: topological rings have continuous ring operations. -/
@[stacks 07E8 "(1), topological ring"]
#check @IsTopologicalRing

/- Definition 15.36.1 (1), tag `07E8`: a topological module has continuous addition and scalar
multiplication. -/
@[stacks 07E8 "(1), topological module"]
#check @IsTopologicalAddGroup
#check @ContinuousSMul

/- Definition 15.36.1 (2), tag `07E8`: homomorphisms of topological modules are continuous
linear maps. -/
@[stacks 07E8 "(2), topological module homomorphism"]
#check @ContinuousLinearMap

/- Definition 15.36.1 (2), tag `07E8`: a homomorphism of topological rings is a continuous ring
homomorphism. -/
section

universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]
  [TopologicalSpace R] [TopologicalSpace S]

@[stacks 07E8 "(2), topological ring homomorphism"]
#check (fun (φ : R →+* S) => Continuous φ)

end

/- Definition 15.36.1 (3), tag `07E8`: linear topologies have a neighborhood basis of
submodules; for a ring these submodules are ideals. -/
@[stacks 07E8 "(3), linearly topologized module or ring"]
#check @IsLinearTopology

/- Definition 15.36.1 (4), tag `07E8`: ideals of definition. -/
@[stacks 07E8 "(4), ideal of definition"]
#check @TopologicalRing.Ideal.IsIdealOfDefinition

/- Definition 15.36.1 (5), tag `07E8`: pre-admissible rings. -/
@[stacks 07E8 "(5), pre-admissible ring"]
#check @TopologicalRing.IsPreadmissibleRing

/- Definition 15.36.1 (6), tag `07E8`: admissible rings. -/
@[stacks 07E8 "(6), admissible ring"]
#check @TopologicalRing.IsAdmissibleRing

/- Definition 15.36.1 (7), tag `07E8`: pre-adic rings. -/
@[stacks 07E8 "(7), pre-adic ring"]
#check @TopologicalRing.IsPreadicRing

/- Definition 15.36.1 (8), tag `07E8`: adic rings. -/
@[stacks 07E8 "(8), adic ring"]
#check @TopologicalRing.IsAdicRing
