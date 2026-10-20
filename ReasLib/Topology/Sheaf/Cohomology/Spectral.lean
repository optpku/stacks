/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.Topology.Sheaf.Cohomology.Restriction
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological dimension of spectral spaces

This leaf owns the Krull-dimension bounds for ordinary sheaf cohomology and cohomology with
support on spectral spaces. It also exposes the degree-at-the-bound surjectivity of restriction to
a compact open.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.Spectral

variable {X : TopCat.{u}} [SpectralSpace X]

/-- On a spectral space of Krull dimension at most `d`, sheaf cohomology vanishes in
every degree strictly larger than `d`. -/
@[stacks 0A3G "cohomological dimension of a spectral space"]
theorem isZero_of_krullDim_le (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ)
    (hXdim : topologicalKrullDim X ≤ d) {q : ℕ} (hq : d < q) :
    IsZero (F.H' q (⊤ : Opens X)) := sorry

/-- In the top degree allowed by a Krull-dimension bound on a spectral space, global
restriction to a compact open is surjective. -/
@[stacks 0A3G "top-degree restriction to a compact open"]
theorem globalRestriction_surjective_of_krullDim_le
    (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ)
    (hXdim : topologicalKrullDim X ≤ d) (U : CompactOpens X) :
    Function.Surjective (globalRestriction F d U.toOpens) := sorry

/-- Global sections with support in a constructible closed subset of a spectral space have
cohomological dimension at most the Krull dimension bound. -/
@[stacks 0A3G "cohomological dimension with constructible closed support"]
theorem supportHasDimensionLE_of_krullDim_le
    (d : ℕ) {Z : Set X} (hZclosed : IsClosed Z)
    (hZconstructible : Topology.IsConstructible Z)
    (hXdim : topologicalKrullDim X ≤ d) :
    ClosedSubset.GlobalSectionsWithSupport.HasDimensionLE hZclosed (d : ℤ) := sorry

/-- Cohomology with support in a constructible closed subset of a spectral space vanishes
above the Krull dimension bound. -/
@[stacks 0A3G "vanishing with constructible closed support"]
theorem support_isZero_of_krullDim_le
    (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ) {Z : Set X}
    (hZclosed : IsClosed Z) (hZconstructible : Topology.IsConstructible Z)
    (hXdim : topologicalKrullDim X ≤ d) {q : ℕ} (hq : d < q) :
    IsZero (ClosedSubset.GlobalSectionsWithSupport.H hZclosed F q) := sorry

end TopCat.Sheaf.Cohomology.Spectral
