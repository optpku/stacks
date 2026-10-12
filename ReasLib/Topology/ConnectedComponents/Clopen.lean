/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Prespectral
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Clopen Descriptions of Connected Components

This module extends Mathlib's compact Hausdorff clopen-neighborhood theorem to
compact prespectral quasi-separated spaces, and packages the corresponding
subset-level saturation criterion.
-/

@[expose] public section

universe u

open Set

variable {X : Type u} [TopologicalSpace X]

namespace Set

/-- A subset is an intersection of clopen subsets. -/
@[stacks 04PL "intersections of open and closed subsets"]
def IsIntersectionOfClopens (T : Set X) : Prop :=
  ∃ S : Set (Set X), (∀ Z ∈ S, IsClopen Z) ∧ T = ⋂₀ S

/-- A subset is saturated under connected components. -/
@[stacks 04PL "unions of connected components"]
def IsConnectedComponentSaturated (T : Set X) : Prop :=
  ∀ x ∈ T, connectedComponent x ⊆ T

/-- An intersection of clopen subsets is closed. -/
theorem IsIntersectionOfClopens.isClosed {T : Set X}
    (hT : T.IsIntersectionOfClopens) : IsClosed T := sorry

/-- An intersection of clopen subsets is saturated under connected components. -/
theorem IsIntersectionOfClopens.isConnectedComponentSaturated {T : Set X}
    (hT : T.IsIntersectionOfClopens) : T.IsConnectedComponentSaturated := sorry

/-- A component-saturated subset contains the connected component of each of its points. -/
theorem IsConnectedComponentSaturated.connectedComponent_subset {T : Set X}
    (hT : T.IsConnectedComponentSaturated) {x : X} (hx : x ∈ T) :
    connectedComponent x ⊆ T := sorry

end Set

namespace PrespectralSpace

/-- In a compact prespectral quasi-separated space, the connected component of a point is the
intersection of all clopen neighborhoods of that point. -/
@[stacks 005F "connected components as intersections of clopen neighborhoods"]
theorem connectedComponent_eq_iInter_isClopen [CompactSpace X] [PrespectralSpace X]
    [QuasiSeparatedSpace X] (x : X) :
    connectedComponent x = ⋂ Z : { Z : Set X // IsClopen Z ∧ x ∈ Z }, Z := sorry

end PrespectralSpace

namespace Set

variable {T : Set X}

/-- A closed component-saturated subset is an intersection of clopen subsets in a compact
prespectral quasi-separated space. -/
@[stacks 04PL "closed unions of connected components are clopen intersections"]
theorem IsClosed.isIntersectionOfClopens
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X]
    (hT : IsClosed T) (hTcomponents : T.IsConnectedComponentSaturated) :
    T.IsIntersectionOfClopens := sorry

/-- In a compact prespectral quasi-separated space, a subset is an intersection of clopen subsets
exactly when it is closed and saturated under connected components. -/
@[stacks 04PL "clopen intersections characterize closed unions of connected components"]
theorem isIntersectionOfClopens_iff
    [CompactSpace X] [PrespectralSpace X] [QuasiSeparatedSpace X] :
    T.IsIntersectionOfClopens ↔ IsClosed T ∧ T.IsConnectedComponentSaturated := sorry

end Set
