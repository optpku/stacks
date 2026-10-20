/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.TopCat.Opens
public import ReasLib.Topology.Category.TopCat.Subset

/-!
# Closed subsets and their open complements

This file owns the coefficient-independent topology used by sections-with-support constructions.
The sheaf-theoretic kernel, functor, and adjunction APIs live in the sibling modules.
-/

@[expose] public section

open TopCat TopologicalSpace

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport

variable {X : TopCat.{u}} {Z : Set X}

/-- The open complement `X \ Z` of a closed subset. -/
abbrev openComplement (hZ : IsClosed Z) : Opens X :=
  ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The inclusion of the open complement of a closed subset into the ambient space. -/
abbrev openComplementInclusion (hZ : IsClosed Z) :
    (Opens.toTopCat X).obj (openComplement hZ) ⟶ X :=
  Opens.inclusion' (openComplement hZ)

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport

end
