module

public import stacks_project.Chap97.Lemma_97_12_1
public import stacks_project.Chap94.Definition_94_12_2_Etale

/-!
# Lemma 97.12.3

In the identity-base specialization of Lemma 97.12.1, an étale (optionally
surjective) 1-morphism `G` induces an étale (optionally surjective) 1-morphism
of finite Hilbert stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.12.3 (1): in the situation of Lemma 97.12.1 with `𝒴' = 𝒴` and
`H = 𝟙 𝒴`, if `G` is representable by algebraic spaces and étale, then the
induced 1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is representable by algebraic
spaces and étale. -/
@[stacks 05YG, instance]
instance finiteHilbertMapSquare.etale (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ)
    [Groupoids.Hom.Etale (asGroupoidsOverMor G)] :
    Groupoids.Hom.Etale
      (asGroupoidsOverMor (finiteHilbertMapSquare F' F G (𝟙 𝒴) γ d)) :=
  sorry

/-- Lemma 97.12.3 (2): in the same situation, if `G` is also surjective, then
the induced 1-morphism `H_d(𝒳'/𝒴) ⟶ H_d(𝒳/𝒴)` is surjective. -/
@[stacks 05YG, instance]
instance finiteHilbertMapSquare.surjective (F' : 𝒳' ⟶ 𝒴) (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (γ : F' ≫ 𝟙 𝒴 ≅ G ≫ F) (d : ℕ)
    [Groupoids.Hom.Etale (asGroupoidsOverMor G)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor G)] :
    Groupoids.Hom.Surjective
      (asGroupoidsOverMor (finiteHilbertMapSquare F' F G (𝟙 𝒴) γ d)) :=
  sorry

end AlgebraicGeometry
