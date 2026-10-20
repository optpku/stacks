module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 65.12.4 (1): let `S` be a scheme and let `F` be an algebraic space over `S`. If
`F₁` and `F₂` are locally closed subspaces of `F`, realized as immersions `i₁ : F₁ ⟶ F` and
`i₂ : F₂ ⟶ F`, and `F₁ ⊂ F₂` as subfunctors of `F` via a morphism `j : F₁ ⟶ F₂` with
`j ≫ i₂ = i₁`, then `F₁` is a locally closed subspace of `F₂`. -/
@[stacks 02YX] #check (AlgebraicGeometry.AlgebraicSpace.IsImmersion.of_comp :
  ∀ {S : Scheme.{u}} {F F₁ F₂ : AlgebraicSpace S}
    (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (j : F₁ ⟶ F₂) [IsImmersion i₁] [IsImmersion i₂],
    j ≫ i₂ = i₁ → IsImmersion j)

/- Lemma 65.12.4 (2): let `S` be a scheme and let `F` be an algebraic space over `S`. If
`F₁` and `F₂` are closed subspaces of `F`, realized as closed immersions `i₁ : F₁ ⟶ F` and
`i₂ : F₂ ⟶ F`, and `F₁ ⊂ F₂` as subfunctors of `F` via a morphism `j : F₁ ⟶ F₂` with
`j ≫ i₂ = i₁`, then `F₁` is a closed subspace of `F₂`. -/
@[stacks 02YX] #check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.of_comp :
  ∀ {S : Scheme.{u}} {F F₁ F₂ : AlgebraicSpace S}
    (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (j : F₁ ⟶ F₂)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂],
    j ≫ i₂ = i₁ → IsClosedImmersion j)

/- Lemma 65.12.4 (3): let `S` be a scheme and let `F` be an algebraic space over `S`. If
`F₁` and `F₂` are open subspaces of `F`, realized as open immersions `i₁ : F₁ ⟶ F` and
`i₂ : F₂ ⟶ F`, and `F₁ ⊂ F₂` as subfunctors of `F` via a morphism `j : F₁ ⟶ F₂` with
`j ≫ i₂ = i₁`, then `F₁` is an open subspace of `F₂`. -/
@[stacks 02YX] #check (AlgebraicGeometry.AlgebraicSpace.IsOpenImmersion.of_comp :
  ∀ {S : Scheme.{u}} {F F₁ F₂ : AlgebraicSpace S}
    (i₁ : F₁ ⟶ F) (i₂ : F₂ ⟶ F) (j : F₁ ⟶ F₂) [IsOpenImmersion i₁] [IsOpenImmersion i₂],
    j ≫ i₂ = i₁ → IsOpenImmersion j)

end AlgebraicGeometry.AlgebraicSpace
