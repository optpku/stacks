module

import StacksCheckRecall
public import stacks_project.Chap71.Lemma_71_12_2_Composition
public import stacks_project.Chap71.Lemma_71_12_2_Map

/-!
# Lemma 71.12.2

Functoriality of relative Proj of algebraic spaces is transitive: the domain of
the composite is the inverse image `r_ψ ⁻¹(U(φ))`, the morphism is the restricted
composite `r_φ ∘ r_ψ`, and the twist comparison is `θ_ψ ∘ r_ψ^* θ_φ`.
-/

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 71.12.2 (1)
The domain of the composite relative-Proj map is the inverse-image open
`r_ψ ⁻¹(U(φ))` in `R`.
-/
@[stacks 085G] #check RelativeProjMap.comp_domain

/- Lemma 71.12.2 (2)
The composite morphism is `r_φ ∘ r_ψ` restricted to `U(ψ ∘ φ)`.
-/
@[stacks 085G] #check RelativeProjMap.comp_map

/- Lemma 71.12.2 (3)
The degreewise twist comparison of the composite is `θ_ψ ∘ r_ψ^* θ_φ`.
-/
@[stacks 085G] #check RelativeProjMap.comp_theta
