module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.OpenCover

/-!
# Locally finite open covers

This module records the canonical open-subset presentation of a locally finite open cover:
`IsOpenCover U ∧ LocallyFinite (Opens.asSets U)`, together with the useful neighborhood
computation API.
-/

@[expose] public section

universe u v

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

namespace TopologicalSpace

namespace Opens

/-- A family of open subsets viewed as its family of underlying sets. -/
abbrev asSets (U : ι → Opens X) : ι → Set X := fun i ↦ U i

/-- Two open subsets meet when their underlying sets are not disjoint. -/
abbrev Meets (U V : Opens X) : Prop := ¬ Disjoint (U : Set X) (V : Set X)

/-- Two open subsets meet exactly when they have a common point. -/
theorem meets_iff {U V : Opens X} : U.Meets V ↔ ∃ x, x ∈ U ∧ x ∈ V := sorry

end Opens

end TopologicalSpace

namespace LocallyFinite

open TopologicalSpace.Opens

/-- A locally finite family of open subsets has, inside every open neighborhood of a point, a
smaller open neighborhood meeting only finitely many family members. -/
theorem exists_open_le_with_finite_nonempty_inter
    {U : ι → Opens X} (hU : LocallyFinite (asSets U))
    (V : Opens X) {x : X} (hx : x ∈ V) :
    ∃ W : Opens X, x ∈ W ∧ W ≤ V ∧ {i | W.Meets (U i)}.Finite := sorry

end LocallyFinite

namespace TopologicalSpace

open Opens

/-- An indexed open cover is locally finite exactly when every
point has an open neighborhood meeting only finitely many cover members. -/
@[stacks 02FS]
theorem locallyFiniteCover_iff (U : ι → Opens X) :
    (IsOpenCover U ∧ LocallyFinite (asSets U)) ↔
      IsOpenCover U ∧ ∀ x : X, ∃ W : Opens X, x ∈ W ∧ {i | W.Meets (U i)}.Finite := sorry

end TopologicalSpace
