module

public import ReasLib.Topology.Spectral.Clopen
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 59.82.3: if `Z` is a closed subset of a spectral space `X` and every trace
`Z ∩ closure ({x} : Set X)` is connected, then every decomposition of `Z` into two disjoint
relatively closed subsets extends to a decomposition of `X` into two disjoint closed subsets. -/
@[stacks 0CAM] #check
  (SpectralSpace.exists_closedPartition :
    ∀ {X : Type u} [TopologicalSpace X] [SpectralSpace X] {Z Z₁ Z₂ : Set X},
      IsClosed Z →
      (∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) →
      Z₁ ⊆ Z →
      Z₂ ⊆ Z →
      IsClosed ((Subtype.val : Z → X) ⁻¹' Z₁) →
      IsClosed ((Subtype.val : Z → X) ⁻¹' Z₂) →
      Z = Z₁ ∪ Z₂ →
      Disjoint Z₁ Z₂ →
      ∃ X₁ X₂ : Set X,
        (Set.univ : Set X) = X₁ ∪ X₂ ∧ Disjoint X₁ X₂ ∧ IsClosed X₁ ∧ IsClosed X₂ ∧
          Z₁ = Z ∩ X₁ ∧ Z₂ = Z ∩ X₂)
