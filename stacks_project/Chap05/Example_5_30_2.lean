/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.CompactOpen
public import ReasLib.Topology.Discrete.Permutation
import StacksCheckRecall

@[expose] public section

open scoped Topology

universe u v

section SelfMaps

variable {E : Type u} [TopologicalSpace E] [DiscreteTopology E]

/- Example 5.30.2 (1): for a discrete domain, `ContinuousMap.homeoFnOfDiscrete` identifies the
compact-open topology on `C(E, E)` with the Pi topology on `E → E`. -/
@[stacks 0BMC "compact-open topology on the self-map space of a discrete set"]
#check (ContinuousMap.homeoFnOfDiscrete : C(E, E) ≃ₜ (E → E))

/- Example 5.30.2 (2): finite agreement sets are a neighborhood basis in the resulting discrete
self-map function space. -/
@[stacks 0BMC "finite-coordinate neighborhood basis for the discrete self-map space"]
#check (fun f : E → E ↦ Pi.nhds_hasBasis_agreeOn_finset_of_discrete f)

/- Example 5.30.2 (3): evaluation is continuous when the function-space domain is discrete. -/
@[stacks 0BMC "continuity of evaluation on the discrete self-map space"]
#check (Pi.continuous_eval_of_discrete :
  Continuous fun p : (E → E) × E ↦ p.1 p.2)

/- Example 5.30.2 (4): continuity of an action map gives continuity of its corresponding family of
self-maps. -/
@[stacks 0BMC "continuity of a family from continuity of its action map"]
#check (fun {X : Type v} [TopologicalSpace X] (f : X → E → E)
  (hf : Continuous fun p : X × E ↦ f p.1 p.2) ↦
  Pi.continuous_of_continuous_uncurry_of_discrete f hf)

/- Example 5.30.2 (5): composition of self-maps is continuous in the compact-open/Pi topology. -/
@[stacks 0BMC "continuity of composition on the discrete self-map space"]
#check (Pi.continuous_comp_of_discrete :
  Continuous fun p : (E → E) × (E → E) ↦ p.1 ∘ p.2)

end SelfMaps

section Automorphisms

variable {E : Type u} [TopologicalSpace E] [DiscreteTopology E]

/- Example 5.30.2 (6): `Equiv.Perm E` has its automatic pointwise topology, with continuous
inversion for discrete `E`. -/
@[stacks 0BMC "continuity of inversion on the discrete automorphism group"]
#check (Equiv.Perm.continuous_inv : Continuous fun σ : Equiv.Perm E ↦ σ⁻¹)

/- Example 5.30.2 (7): the pointwise topology makes `Equiv.Perm E` a topological group. -/
@[stacks 0BMC "the automorphism group of a discrete set is a topological group"]
#check (inferInstance : IsTopologicalGroup (Equiv.Perm E))

end Automorphisms
