/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.ContinuousMap.T0Sierpinski
public import ReasLib.Topology.ConstructibleTopology.Maps
public import ReasLib.Topology.Spectral.Subspace

/-!
# Compact-Open Sierpinski Representations

The compact-open membership map is the canonical representation of a
prespectral space in a product of Sierpinski spaces.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology

namespace TopologicalSpace

/-- The compact-open membership map is continuous. -/
theorem continuous_compactOpenMembershipMap
    (X : Type u) [TopologicalSpace X] :
    Continuous fun x : X ↦ fun U : CompactOpens X ↦ x ∈ (U : Set X) := sorry

/-- Lemma 5.23.13: the canonical map from a space to the Sierpinski product
indexed by its compact open subsets. -/
@[stacks 09XW "compact-open Sierpinski representation"]
def compactOpenMembershipMap
    (X : Type u) [TopologicalSpace X] : C(X, CompactOpens X → Prop) :=
  ⟨fun x U ↦ x ∈ (U : Set X), continuous_compactOpenMembershipMap X⟩

/-- Evaluation of the compact-open membership map is membership in the compact
open subset. -/
@[simp]
theorem compactOpenMembershipMap_apply
    (X : Type u) [TopologicalSpace X] (x : X) (U : CompactOpens X) :
    compactOpenMembershipMap X x U ↔ x ∈ (U : Set X) := sorry

/-- When compact opens form a basis, the compact-open membership map is
inducing. -/
theorem compactOpenMembershipMap_isInducing
    (X : Type u) [TopologicalSpace X] [PrespectralSpace X] :
    IsInducing (compactOpenMembershipMap X) := sorry

/-- In a `T₀` prespectral space, compact-open membership separates points. -/
theorem compactOpenMembershipMap_injective
    (X : Type u) [TopologicalSpace X] [PrespectralSpace X] [T0Space X] :
    Function.Injective (compactOpenMembershipMap X) := sorry

/-- In a `T₀` prespectral space, the compact-open membership map is an
embedding. -/
theorem compactOpenMembershipMap_isEmbedding
    (X : Type u) [TopologicalSpace X] [PrespectralSpace X] [T0Space X] :
    IsEmbedding (compactOpenMembershipMap X) := sorry

/-- For a spectral space, the compact-open membership map is spectral. -/
theorem compactOpenMembershipMap_isSpectralMap
    (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    IsSpectralMap (compactOpenMembershipMap X) := sorry

/-- The range of the compact-open membership map of a spectral space is closed
in the constructible topology of its Sierpinski product. -/
theorem isClosed_range_compactOpenMembershipMap_constructibleTopology
    (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    IsClosed[constructibleTopology (CompactOpens X → Prop)]
      (Set.range (compactOpenMembershipMap X)) := sorry

end TopologicalSpace

namespace SpectralSpace

/-- Lemma 5.23.13: a topological space is spectral exactly when it is
homeomorphic to a constructibly closed subspace of a Sierpinski product. -/
@[stacks 09XW]
theorem iff_homeomorphic_constructiblyClosed_sierpinskiProduct
    (X : Type u) [TopologicalSpace X] :
    SpectralSpace X ↔
      ∃ (ι : Type u) (E : Set (ι → Prop)),
        IsClosed[constructibleTopology (ι → Prop)] E ∧ Nonempty (X ≃ₜ E) := sorry

end SpectralSpace
