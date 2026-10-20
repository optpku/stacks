/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Bases
public import ReasLib.AlgebraicGeometry.Scheme.Topology.MinimalSpecialization

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Every infinite dense subset of a Noetherian scheme contains a countable dense subset. -/
theorem exists_countable_dense_subset_of_infinite_dense
    {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {T : Set S}
    (hT_dense : Dense T) (hT_infinite : T.Infinite) :
    ∃ E ⊆ T, E.Countable ∧ Dense E := sorry

end AlgebraicGeometry.Scheme
