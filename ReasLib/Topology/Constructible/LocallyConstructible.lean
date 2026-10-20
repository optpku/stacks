/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible

/-!
# Locally Constructible Sets

This module records closure properties of locally constructible subsets of a
topological space.
-/

@[expose] public section

universe u

open Set

namespace Topology

variable {X : Type u} [TopologicalSpace X] {E : Set X}

/-- The complement of a locally constructible subset is locally constructible. -/
theorem IsLocallyConstructible.compl (hE : IsLocallyConstructible E) :
    IsLocallyConstructible Eᶜ := sorry

end Topology
