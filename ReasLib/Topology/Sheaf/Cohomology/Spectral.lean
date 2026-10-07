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

/-- Proposition 20.22.4 (0A3G) (1): on a spectral space of Krull dimension at most `d`,
cohomology vanishes in every degree strictly larger than `d`. -/
@[stacks 0A3G "cohomological dimension of a spectral space"]
theorem isZero_of_krullDim_le (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ)
    (hXdim : topologicalKrullDim X ≤ d) {q : ℕ} (hq : d < q) :
    IsZero (F.H' q (⊤ : Opens X)) := sorry

/-- Proposition 20.22.4 (0A3G) (2): in the top degree allowed by a Krull-dimension bound,
global restriction to a compact open is surjective. -/
@[stacks 0A3G "top-degree restriction to a compact open"]
theorem globalRestriction_surjective_of_krullDim_le
    (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ)
    (hXdim : topologicalKrullDim X ≤ d) (U : CompactOpens X) :
    Function.Surjective (globalRestriction F d U.toOpens) := sorry

/-- Functorial form of Proposition 20.22.4 (0A3G) (3): global sections with support in a
constructible closed subset have cohomological dimension at most the Krull dimension bound. -/
@[stacks 0A3G "cohomological dimension with constructible closed support"]
theorem supportHasDimensionLE_of_krullDim_le
    (d : ℕ) {Z : Set X} (hZclosed : IsClosed Z)
    (hZconstructible : Topology.IsConstructible Z)
    (hXdim : topologicalKrullDim X ≤ d) :
    ClosedSubset.GlobalSectionsWithSupport.HasDimensionLE hZclosed (d : ℤ) := sorry

/-- Proposition 20.22.4 (0A3G) (3): cohomology with support in a constructible closed subset
vanishes above the Krull dimension bound. -/
@[stacks 0A3G "vanishing with constructible closed support"]
theorem support_isZero_of_krullDim_le
    (F : X.Sheaf AddCommGrpCat.{u}) (d : ℕ) {Z : Set X}
    (hZclosed : IsClosed Z) (hZconstructible : Topology.IsConstructible Z)
    (hXdim : topologicalKrullDim X ≤ d) {q : ℕ} (hq : d < q) :
    IsZero (ClosedSubset.GlobalSectionsWithSupport.H hZclosed F q) := sorry

end TopCat.Sheaf.Cohomology.Spectral
