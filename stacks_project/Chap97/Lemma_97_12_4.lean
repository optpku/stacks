module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Etale
import StacksCheckRecall

/-!
# Lemma 97.12.4

For positive degree, in the situation of Lemma 97.12.1, if `G` and `H` are representable by
algebraic spaces and étale, then the induced 1-morphism of finite Hilbert
stacks is representable by algebraic spaces and étale, and it is surjective
when `H` and the induced functor `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` are surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

universe u

/- Lemma 97.12.4 (1): in the situation of Lemma 97.12.1, if `G` and `H` are
representable by algebraic spaces and étale, then the induced 1-morphism
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)` is representable by algebraic spaces and étale
for positive degree. -/
@[stacks 05XS] #check
  (AlgebraicGeometry.finiteHilbertMapSquare.etaleOfSquare :
    ∀ {S : Scheme.{u}} {𝒳' 𝒳 𝒴' 𝒴 :
      StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
      (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
      (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) [NeZero d]
      [Groupoids.Hom.Etale (asGroupoidsOverMor G)]
      [Groupoids.Hom.Etale (asGroupoidsOverMor H)],
      Groupoids.Hom.Etale
        (asGroupoidsOverMor (finiteHilbertMapSquare F' F G H γ d)))

/- Lemma 97.12.4 (2): in the same situation, if also `H` is surjective and the
induced functor `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` is surjective, then
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)` is surjective for positive degree. -/
@[stacks 05XS] #check
  (AlgebraicGeometry.finiteHilbertMapSquare.surjectiveOfSquare :
    ∀ {S : Scheme.{u}} {𝒳' 𝒳 𝒴' 𝒴 :
      StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
      (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴)
      (γ : F' ≫ H ≅ G ≫ F) (d : ℕ) [NeZero d]
      [Groupoids.Hom.Etale (asGroupoidsOverMor G)]
      [Groupoids.Hom.Etale (asGroupoidsOverMor H)]
      [Groupoids.Hom.Surjective (asGroupoidsOverMor H)]
      [Groupoids.Hom.Surjective (asGroupoidsOverMor
        (CategoryTheory.Bicategory.PseudoPullbackCone.lift
          (CategoryTheory.Bicategory.PseudoPullbackCone.mk H F 𝒳' F' G γ)
          (CategoryTheory.StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u}
            H F)))],
      Groupoids.Hom.Surjective
        (asGroupoidsOverMor (finiteHilbertMapSquare F' F G H γ d)))
