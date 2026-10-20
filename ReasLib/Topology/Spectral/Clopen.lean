module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Connected.Basic

@[expose] public section

universe u

namespace SpectralSpace

/-- A relatively closed partition of a closed subset extends to a closed partition of the space
when each point closure meets the subset in a connected nonempty set. -/
theorem exists_closedPartition
    {X : Type u} [TopologicalSpace X] [SpectralSpace X] {Z Z₁ Z₂ : Set X}
    (hZ : IsClosed Z)
    (hconn : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (hZ₁ : Z₁ ⊆ Z)
    (hZ₂ : Z₂ ⊆ Z)
    (hZ₁_closed : IsClosed ((Subtype.val : Z → X) ⁻¹' Z₁))
    (hZ₂_closed : IsClosed ((Subtype.val : Z → X) ⁻¹' Z₂))
    (hdecomp : Z = Z₁ ∪ Z₂)
    (hdisjoint : Disjoint Z₁ Z₂) :
    ∃ X₁ X₂ : Set X,
      (Set.univ : Set X) = X₁ ∪ X₂ ∧ Disjoint X₁ X₂ ∧ IsClosed X₁ ∧ IsClosed X₂ ∧
        Z₁ = Z ∩ X₁ ∧ Z₂ = Z ∩ X₂ := sorry

end SpectralSpace
