module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.RelativeRepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.FiniteHilbertStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

/- Lemma 97.12.5: For a 1-morphism `F : 𝒳 ⟶ 𝒴` of stacks in groupoids over
`(Sch/S)_fppf` and positive degree `d`, representability by algebraic spaces of
the object diagonal of `𝒴` implies representability by algebraic spaces of the
forgetful pairing `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 95.18.2.1. -/
@[stacks 05YH] #check
  (AlgebraicGeometry.FiniteHilbertStack.forgetToProduct.relativelyRepresentableByAlgebraicSpaces :
    {S : Scheme.{u}} →
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)} →
    (F : 𝒳 ⟶ 𝒴) → (d : ℕ) → (hd : 1 ≤ d) →
    (h_diagonal : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (asGroupoidsOver 𝒴))) →
    relativelyRepresentableByAlgebraicSpaces (forgetToProduct F d))

