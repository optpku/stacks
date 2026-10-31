/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sets.Opens

/-!
# Locally Noetherian Spaces

This leaf extends Mathlib's global `TopologicalSpace.NoetherianSpace` with
the local form and its basic permanence and consequence API.
-/

@[expose] public section

universe u v

open Topology

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- A topological space is locally Noetherian if every point has an open
neighbourhood whose induced topology is Noetherian. -/
@[stacks 0051 "locally Noetherian topological spaces"]
class LocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Every point lies in an open Noetherian subspace. -/
  exists_open (x : X) : ∃ U : Opens X, x ∈ U ∧ NoetherianSpace U

/-- The defining open-neighbourhood condition for a locally Noetherian space. -/
theorem locallyNoetherianSpace_iff :
    LocallyNoetherianSpace X ↔
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧ NoetherianSpace U :=
  ⟨fun h => h.exists_open, fun h => ⟨h⟩⟩

/-- Every neighbourhood of a point in a locally Noetherian space contains an open Noetherian
neighbourhood. -/
theorem LocallyNoetherianSpace.exists_open_subset [LocallyNoetherianSpace X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ U : Opens X, x ∈ U ∧ (U : Set X) ⊆ s ∧ NoetherianSpace U := sorry

/-- Every neighbourhood of a point in a locally Noetherian space contains a Noetherian
neighbourhood. -/
theorem LocallyNoetherianSpace.exists_mem_nhds_subset [LocallyNoetherianSpace X] (x : X)
    {s : Set X} (hs : s ∈ 𝓝 x) :
    ∃ t : Set X, t ∈ 𝓝 x ∧ t ⊆ s ∧ NoetherianSpace t := sorry

/-- Every point of a locally Noetherian space has a Noetherian member of its neighbourhood
filter. -/
theorem LocallyNoetherianSpace.exists_mem_nhds [LocallyNoetherianSpace X] (x : X) :
    ∃ s : Set X, s ∈ 𝓝 x ∧ NoetherianSpace s := sorry

/-- Every subspace of a locally Noetherian space is locally Noetherian. -/
instance LocallyNoetherianSpace.set (S : Set X) [LocallyNoetherianSpace X] :
    LocallyNoetherianSpace S := sorry

/-- Local Noetherianity transports along a homeomorphism. -/
theorem _root_.Homeomorph.locallyNoetherianSpace
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) [LocallyNoetherianSpace X] :
    LocallyNoetherianSpace Y := sorry

/-- Local Noetherianity is invariant under homeomorphism. -/
theorem _root_.Homeomorph.locallyNoetherianSpace_iff
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    LocallyNoetherianSpace X ↔ LocallyNoetherianSpace Y := sorry

/-- Every Noetherian topological space is locally Noetherian. -/
instance NoetherianSpace.locallyNoetherianSpace [NoetherianSpace X] :
    LocallyNoetherianSpace X := sorry

/-- The image of a locally Noetherian space under a continuous open map is locally
Noetherian for its induced topology. -/
@[stacks 04Z8 "open continuous images of locally Noetherian spaces"]
theorem LocallyNoetherianSpace.range {Y : Type v} [TopologicalSpace Y] {f : X → Y}
    [LocallyNoetherianSpace X] (hcont : Continuous f) (hopen : IsOpenMap f) :
    LocallyNoetherianSpace (Set.range f) := sorry

/-- Every locally Noetherian topological space is locally connected. -/
@[stacks 04MF]
instance LocallyNoetherianSpace.locallyConnectedSpace [LocallyNoetherianSpace X] :
    LocallyConnectedSpace X := sorry

/-- A compact locally Noetherian topological space is Noetherian. -/
@[stacks 04ZB]
theorem LocallyNoetherianSpace.noetherianSpace
    [CompactSpace X] [LocallyNoetherianSpace X] :
    NoetherianSpace X := sorry

attribute [instance 100] LocallyNoetherianSpace.noetherianSpace

end TopologicalSpace
