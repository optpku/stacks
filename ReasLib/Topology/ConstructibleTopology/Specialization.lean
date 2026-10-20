/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.ConstructibleTopology.Spectral

/-!
# Specialization-Stable Constructible-Topology Sets

This module relates patch-closed and patch-open subsets of a spectral space to
ordinary specialization and generalization stability.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] [SpectralSpace X]

namespace IsClosed

/-- A point in the ordinary closure of a constructibly closed subset is a
specialization of a point of that subset. -/
@[stacks 0903 "specialization from a constructibly closed subset"]
theorem exists_specializingPoint_of_mem_closure
    {E : Set X} (hE : IsClosed[constructibleTopology X] E) {x : X}
    (hx : x ∈ closure E) :
    ∃ y ∈ E, y ⤳ x := sorry

/-- A constructibly closed specialization-stable subset of a spectral space is
closed in the original topology. -/
@[stacks 0903 "specialization-stable patch closed subsets"]
theorem isClosed_of_constructibleTopology_of_stableUnderSpecialization
    {E : Set X} (hE : IsClosed[constructibleTopology X] E)
    (hE_spec : StableUnderSpecialization E) :
    IsClosed E := sorry

end IsClosed

namespace IsOpen

/-- A constructibly open generalization-stable subset of a spectral space is
open in the original topology. -/
@[stacks 0903 "generalization-stable patch open subsets"]
theorem isOpen_of_constructibleTopology_of_stableUnderGeneralization
    {E : Set X} (hE : IsOpen[constructibleTopology X] E)
    (hE_gen : StableUnderGeneralization E) :
    IsOpen E := sorry

end IsOpen
