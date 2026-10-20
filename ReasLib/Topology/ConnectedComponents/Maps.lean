/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.ConnectedComponents.Clopen

/-!
# Maps on Connected Components

This module records how continuous maps interact with connected components, together with
hypothesis-level bridges to Mathlib's `Topology.IsCoinducing.connectedComponentsMap_bijective`
theorem.
-/

@[expose] public section

universe u v

open Set Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- Stacks tag 0377: a continuous map with connected fibers and a closed-set quotient characterization induces a
bijective map on connected components. The continuity hypothesis is kept explicit so callers can
reuse the resulting map and its associated continuous-map API directly. -/
@[stacks 0377]
theorem connectedComponentsMap_bijective_of_isClosed_iff_preimage
    (hcont : Continuous f) (hfiber : ∀ y : Y, IsConnected (f ⁻¹' {y}))
    (hclosed : ∀ T : Set Y, IsClosed T ↔ IsClosed (f ⁻¹' T)) :
    hcont.connectedComponentsMap.Bijective := sorry

/-- An open continuous map with connected fibers induces a bijection on connected components. -/
@[stacks 0378]
theorem Continuous.connectedComponentsMap_bijective_of_isOpenMap_of_connectedFibers
    (hcont : Continuous f) (hopen : IsOpenMap f)
    (hfibers : ∀ y : Y, IsConnected (f ⁻¹' {y})) :
    hcont.connectedComponentsMap.Bijective := sorry

/-- The preimage of a connected component under a continuous map is saturated under connected
components. -/
theorem Continuous.preimage_connectedComponent_isConnectedComponentSaturated
    (hcont : Continuous f) (y : Y) :
    Set.IsConnectedComponentSaturated (f ⁻¹' connectedComponent y) := sorry
