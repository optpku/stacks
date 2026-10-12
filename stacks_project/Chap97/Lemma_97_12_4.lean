/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Lemma_97_12_4_FibreProduct
public import stacks_project.Chap97.Lemma_97_12_1
public import stacks_project.Chap94.Definition_94_12_2_Etale

/-!
# Lemma 97.12.4

In the situation of Lemma 97.12.1, if `G` and `H` are representable by
algebraic spaces and étale, then the induced 1-morphism of finite Hilbert
stacks is representable by algebraic spaces and étale, and it is surjective
when `H` and the induced functor `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` are surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.12.4 (1): in the situation of Lemma 97.12.1, if `G` and `H` are
representable by algebraic spaces and étale, then the induced 1-morphism
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)` is representable by algebraic spaces and étale. -/
@[stacks 05XS, instance]
instance finiteHilbertMapSquare.etale (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    [Groupoids.Hom.Etale (asGroupoidsOverMor G)]
    [Groupoids.Hom.Etale (asGroupoidsOverMor H)] :
    Groupoids.Hom.Etale
      (asGroupoidsOverMor (finiteHilbertMapSquare F' F G H γ d)) :=
  sorry

/-- Lemma 97.12.4 (2): in the same situation, if also `H` is surjective and the
induced functor `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` is surjective, then
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)` is surjective. -/
@[stacks 05XS, instance]
instance finiteHilbertMapSquare.surjective (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    [Groupoids.Hom.Etale (asGroupoidsOverMor G)]
    [Groupoids.Hom.Etale (asGroupoidsOverMor H)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor H)]
    [Groupoids.Hom.Surjective (asGroupoidsOverMor (toFibreProduct F' F G H γ))] :
    Groupoids.Hom.Surjective
      (asGroupoidsOverMor (finiteHilbertMapSquare F' F G H γ d)) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
