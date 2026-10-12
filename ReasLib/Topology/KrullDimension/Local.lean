/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.LocalAtTarget
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local topological Krull dimension

This module owns the local Krull dimension of a point of a topological space and its basic
specialization and transport API.
-/

@[expose] public section

universe u v

open Set TopologicalSpace Order

variable {X : Type u} [TopologicalSpace X]

/-- The poset of irreducible closed subsets is empty exactly when the ambient space is empty. -/
theorem isEmpty_irreducibleCloseds_iff :
    IsEmpty (IrreducibleCloseds X) ↔ IsEmpty X := sorry

/-- The topological Krull dimension is bottom exactly for an empty space. -/
theorem topologicalKrullDim_eq_bot_iff :
    topologicalKrullDim X = ⊥ ↔ IsEmpty X := sorry

/-- The local topological Krull dimension at `x`, computed as the infimum of the dimensions of
its open neighbourhoods. -/
@[stacks 0055 "local Krull dimension at a point"]
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ U : OpenNhdsOf x, topologicalKrullDim U

/-- The local topological Krull dimension is attained by an open neighbourhood and is bounded by
the dimension of every open neighbourhood. -/
theorem isLeast_topologicalKrullDimAt (x : X) :
    IsLeast (Set.range fun U : OpenNhdsOf x ↦ topologicalKrullDim U)
      (topologicalKrullDimAt x) := sorry

/-- The local topological Krull dimension is bounded above by every open neighbourhood
dimension. -/
theorem topologicalKrullDimAt_le (x : X) (U : OpenNhdsOf x) :
    topologicalKrullDimAt x ≤ topologicalKrullDim U := sorry

/-- Some open neighbourhood realizes the local topological Krull dimension. -/
theorem exists_openNhdsOf_topologicalKrullDimAt_eq (x : X) :
    ∃ U : OpenNhdsOf x, topologicalKrullDimAt x = topologicalKrullDim U := sorry

/-- Local topological Krull dimension is monotone along specialization. -/
theorem Specializes.topologicalKrullDimAt_le {x y : X} (hxy : x ⤳ y) :
    topologicalKrullDimAt x ≤ topologicalKrullDimAt y := sorry

section Transport

variable {Y : Type v} [TopologicalSpace Y]

/-- An open embedding preserves local topological Krull dimension. -/
theorem topologicalKrullDimAt_eq_of_isOpenEmbedding
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) (x : X) :
    topologicalKrullDimAt (f x) = topologicalKrullDimAt x := sorry

/-- Passing to an open subspace preserves local topological Krull dimension. -/
theorem topologicalKrullDimAt_subtype_eq_of_isOpen
    {U : Set X} (hU : IsOpen U) (x : U) :
    topologicalKrullDimAt x = topologicalKrullDimAt (x : X) := sorry

/-- A homeomorphism preserves local topological Krull dimension. -/
theorem topologicalKrullDimAt_eq_of_homeomorph (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt (e x) = topologicalKrullDimAt x := sorry

end Transport

/-- Local topological Krull dimension is bounded above by the dimension of the ambient space. -/
theorem topologicalKrullDimAt_le_topologicalKrullDim (x : X) :
    topologicalKrullDimAt x ≤ topologicalKrullDim X := sorry

/-- Global topological Krull dimension is the supremum of the local dimensions at all points. -/
@[stacks 0B7I "global topological Krull dimension as a supremum of local dimensions"]
theorem topologicalKrullDim_eq_iSup_topologicalKrullDimAt :
    topologicalKrullDim X = ⨆ x : X, topologicalKrullDimAt x := sorry

/-- Local topological Krull dimension is nonnegative. -/
theorem topologicalKrullDimAt_nonneg (x : X) :
    0 ≤ topologicalKrullDimAt x := sorry

/-- Local topological Krull dimension is never bottom. -/
@[simp]
theorem topologicalKrullDimAt_ne_bot (x : X) :
    topologicalKrullDimAt x ≠ ⊥ := sorry
