/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Group.GroupTopology
public import Mathlib.Topology.Maps.Basic
public import ReasLib.Topology.Discrete.FunctionSpace

/-!
# Pointwise topology on permutation groups

The pointwise topology on `Equiv.Perm E` is induced by the inclusion into `E → E`.  When `E` is
discrete, it makes the permutation group a topological group.
-/

@[expose] public section

universe u

namespace Equiv.Perm

variable {E : Type u} [TopologicalSpace E]

/-- The pointwise topology on permutations, induced by their underlying functions. -/
@[stacks 0BMC "pointwise topology on a permutation group"]
def pointwiseTopology : TopologicalSpace (Equiv.Perm E) :=
  TopologicalSpace.induced (fun σ : Equiv.Perm E ↦ (σ : E → E)) inferInstance

section Discrete

variable [DiscreteTopology E]

/-- The pointwise topology is canonical on the permutation group of a discrete space. -/
@[stacks 0BMC "pointwise topology on a discrete permutation group"]
instance pointwiseTopologicalSpace : TopologicalSpace (Equiv.Perm E) :=
  pointwiseTopology

/-- The inclusion of permutations into the Pi function space is continuous for the pointwise
topology of a discrete space. -/
@[stacks 0BMC "continuous inclusion of permutations into the function space"]
theorem continuous_coe : Continuous fun σ : Equiv.Perm E ↦ (σ : E → E) := sorry

/-- The pointwise topology is inducing along the inclusion into the Pi function space. -/
@[stacks 0BMC "inducing pointwise discrete permutation topology"]
theorem isInducing_coe : Topology.IsInducing fun σ : Equiv.Perm E ↦ (σ : E → E) := sorry

/-- Inversion of permutations is continuous for the pointwise topology of a discrete space. -/
@[stacks 0BMC "continuity of inversion on a discrete permutation group"]
theorem continuous_inv : Continuous fun σ : Equiv.Perm E ↦ σ⁻¹ := sorry

/-- Multiplication of permutations is continuous for the pointwise topology of a discrete space. -/
@[stacks 0BMC "continuity of multiplication on a discrete permutation group"]
theorem continuous_mul : Continuous fun p : Equiv.Perm E × Equiv.Perm E ↦ p.1 * p.2 := sorry

end Discrete

/-- The pointwise permutation group of a discrete space is a topological group. -/
@[stacks 0BMC "topological group of permutations of a discrete space"]
instance isTopologicalGroup {E : Type u} [TopologicalSpace E] [DiscreteTopology E] :
    IsTopologicalGroup (Equiv.Perm E) := sorry


end Equiv.Perm
