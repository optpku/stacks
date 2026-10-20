/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Nowhere dense preimages under open maps

This module owns the transport of nowhere denseness along continuous open maps.
The result is stated for `IsOpenMap` and `Continuous` separately because mathlib
does not package this pair into a canonical bundled map type.
-/

@[expose] public section

open Set Topology

universe u v

section

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f : X → Y} {T : Set Y}

namespace IsOpenMap

/-- Lemma 5.21.6 (1), tag 03HR: a continuous open map pulls back nowhere dense subsets to
nowhere dense subsets. -/
@[stacks 03HR "nowhere dense preimages under continuous open maps"]
theorem isNowhereDense_preimage
    (hf : IsOpenMap f) (hcont : Continuous f) (hT : IsNowhereDense T) :
    IsNowhereDense (f ⁻¹' T) := sorry

/-- Lemma 5.21.6 (1), tag 03HR: a continuous open map pulls back closed nowhere dense subsets
to closed nowhere dense subsets. -/
@[stacks 03HR "closed nowhere dense preimages under continuous open maps"]
theorem isClosed_isNowhereDense_preimage
    (hf : IsOpenMap f) (hcont : Continuous f) (hT : IsClosed T ∧ IsNowhereDense T) :
    IsClosed (f ⁻¹' T) ∧ IsNowhereDense (f ⁻¹' T) := sorry

end IsOpenMap

end
