/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeaklyAdmissible

@[expose] public section

universe u

#check (TopologicalRing.Ideal.IsWeakIdealOfDefinition :
  ∀ {R : Type u} [CommRing R] [TopologicalSpace R], Ideal R → Prop)
