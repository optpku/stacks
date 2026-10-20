/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Sets.Opens

/-!
# Tuple-controlled open covers

This leaf owns the part of a tuplewise shrinking which is independent of the
separation or compactness hypotheses used to construct it.
-/

@[expose] public section

open Set

universe u v

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {I : Type v}

/-- An open family covering a specified subset whose fixed finite intersections are contained in
prescribed open subsets. -/
@[stacks 09UX "tuple-controlled open cover predicate"]
structure IsTuplewiseOpenCover
    (Z : Set X) (p : ℕ) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) : Prop where
  /-- The family covers the specified subset. -/
  cover : Z ⊆ ⋃ i, (V i : Set X)
  /-- Each displayed tuple intersection is contained in its prescribed open subset. -/
  tuplewise_subset (σ : Fin (p + 1) → I) :
    (⋂ j, (V (σ j) : Set X)) ⊆ W σ

/-- The cover and tuplewise-containment conditions defining a tuple-controlled open cover. -/
@[stacks 09UX]
theorem isTuplewiseOpenCover_iff
    (Z : Set X) (p : ℕ) (W : (Fin (p + 1) → I) → Opens X)
    (V : I → Opens X) :
    IsTuplewiseOpenCover Z p W V ↔
      Z ⊆ ⋃ i, (V i : Set X) ∧
        ∀ σ : Fin (p + 1) → I, (⋂ j, (V (σ j) : Set X)) ⊆ W σ := sorry

end TopologicalSpace
