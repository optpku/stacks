module

public import Mathlib.Order.Filter.Pi
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Instances.Discrete

/-!
# Function spaces indexed by discrete spaces

This module collects the pointwise-topology facts whose extra continuity is caused by a discrete
index or codomain.  The owners are the ordinary Pi types, rather than a chapter-specific space of
self-maps.
-/

@[expose] public section

open Filter
open scoped Topology

universe u v w

namespace Pi

section DiscreteCodomain

variable {ι : Type u} {X : Type v} [TopologicalSpace X] [DiscreteTopology X]

/-- Neighborhoods in a Pi type with discrete codomain have a basis of finite agreement sets. -/
@[stacks 0BMC "finite-coordinate neighborhoods in a discrete function space"]
theorem nhds_hasBasis_agreeOn_of_discrete (f : ι → X) :
    (𝓝 f).HasBasis Set.Finite (fun s ↦ {g | ∀ i ∈ s, g i = f i}) := sorry

/-- The finite-agreement neighborhood basis indexed by `Finset` rather than finite sets. -/
@[stacks 0BMC "finite-coordinate neighborhoods indexed by finite sets"]
theorem nhds_hasBasis_agreeOn_finset_of_discrete (f : ι → X) :
    (𝓝 f).HasBasis (fun _ : Finset ι ↦ True)
      (fun s ↦ {g | ∀ i ∈ s, g i = f i}) := sorry

end DiscreteCodomain

section DiscreteDomain

variable {ι : Type u} {X : Type v} [TopologicalSpace ι] [DiscreteTopology ι]
  [TopologicalSpace X]

/-- Evaluation on a Pi type is continuous when its index space is discrete. -/
@[stacks 0BMC "continuity of evaluation for a discrete function-space domain"]
theorem continuous_eval_of_discrete :
    Continuous fun p : (ι → X) × ι ↦ p.1 p.2 := sorry

/-- A family of functions on a discrete space is continuous once its uncurried action is
continuous. -/
@[stacks 0BMC "continuity of a family from continuity of its action on a discrete space"]
theorem continuous_of_continuous_uncurry_of_discrete {Z : Type w} [TopologicalSpace Z]
    (f : Z → ι → X) (hf : Continuous fun p : Z × ι ↦ f p.1 p.2) : Continuous f := sorry

end DiscreteDomain

section Composition

variable {ι : Type u} {κ : Type v} {X : Type w} [TopologicalSpace κ] [DiscreteTopology κ]
  [TopologicalSpace X]

/-- Composition is continuous when the intermediate function-space domain is discrete. -/
@[stacks 0BMC "continuity of composition through a discrete space"]
theorem continuous_comp_of_discrete :
    Continuous fun p : (κ → X) × (ι → κ) ↦ p.1 ∘ p.2 := sorry

end Composition

end Pi
