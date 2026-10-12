/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.LocallyFinite
public import ReasLib.Topology.Stratification.Indexed

/-!
# Closed initial families and their frontier stratifications
-/

@[expose] public section

universe u v

open Set

variable {X : Type u} [TopologicalSpace X]
variable {I : Type v} [PartialOrder I]

/-- A closed covering family whose intersections are the unions of the common lower stages. -/
@[stacks 09Y2 "closed initial family"]
structure IsClosedInitialFamily (Z : I → Set X) : Prop where
  /-- Each stage is closed. -/
  isClosed (i : I) : IsClosed (Z i)
  /-- The stages cover the ambient space. -/
  iUnion_eq_univ : ⋃ i, Z i = univ
  /-- Intersections are unions of common lower stages. -/
  inter_eq_iUnion (i j : I) :
    Z i ∩ Z j = ⋃ k ∈ Iic i ∩ Iic j, Z k

/-- The defining closedness, covering, and intersection conditions of a closed initial family. -/
theorem isClosedInitialFamily_iff {Z : I → Set X} :
    IsClosedInitialFamily Z ↔
      (∀ i, IsClosed (Z i)) ∧
      (⋃ i, Z i) = univ ∧
      ∀ i j, Z i ∩ Z j = ⋃ k ∈ Iic i ∩ Iic j, Z k := sorry

namespace IsStratification

/-- The lower initial union attached to an indexed family of strata. -/
abbrev initial (strata : I → Set X) (i : I) : Set X :=
  ⋃ j ∈ Iic i, strata j

/-- Locally finite stratifications produce closed initial families. -/
@[stacks 09Y2 "initial closed family from locally finite strata"]
theorem initial_isClosedInitialFamily
    {strata : I → Set X} (hstrata : IsStratification strata) (hloc : LocallyFinite strata) :
    IsClosedInitialFamily (initial strata) := sorry

end IsStratification

namespace IsClosedInitialFamily

/-- The frontier difference at a stage of a closed initial family. -/
abbrev frontier (Z : I → Set X) (i : I) : Set X :=
  Z i \ ⋃ j ∈ Iio i, Z j

/-- The indices with nonempty frontier differences. -/
abbrev FrontierIndex (Z : I → Set X) : Type v :=
  { i : I // (frontier Z i).Nonempty }

/-- The family of nonempty frontier differences. -/
abbrev frontierStrata (Z : I → Set X) : FrontierIndex Z → Set X :=
  fun i ↦ frontier Z i.1

/-- A point cannot lie in two different frontier differences. -/
theorem frontierIndex_eq_of_mem
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) {i j : I} {x : X}
    (hxi : x ∈ frontier Z i) (hxj : x ∈ frontier Z j) :
    i = j := sorry

/-- Locally finite closed initial families produce locally finite frontier stratifications. -/
@[stacks 09Y2 "locally finite frontier stratification from closed initial subsets"]
theorem frontier_isStratification
    {Z : I → Set X} (hZ : IsClosedInitialFamily Z) (hloc : LocallyFinite Z) :
    IsStratification (frontierStrata Z) ∧ LocallyFinite (frontierStrata Z) := sorry

end IsClosedInitialFamily
