/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap97.«97_6_0_1_Lifting»
public import stacks_project.Chap97.Lemma_97_15_4_Lci
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Lemma 97.15.3

If `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
that is representable by algebraic spaces, flat, and locally of finite
presentation, then `p : H_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is formally smooth on objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 97.15.3: if `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over
`(Sch/S)_fppf` that is representable by algebraic spaces, flat, and locally of
finite presentation, then the LCI forgetful 1-morphism
`p = lciForgetToY F d : H_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is formally smooth on objects.
The hypotheses `Flat` and `LocallyOfFinitePresentation` each include relative
representability by algebraic spaces. -/
@[stacks 06D9]
instance lciForgetToY.formallySmoothOnObjects (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] :
    Groupoids.Hom.FormallySmoothOnObjects
      (asGroupoidsOverMor (lciForgetToY F d)) :=
  sorry

/-- An affine first-order infinitesimal lifting problem for
`lciForgetToY F d` admits a solution making the restriction square commute. -/
theorem lciForgetToY.formallySmoothOnObjects_spec (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.FormallySmoothOnObjects
      (asGroupoidsOverMor (lciForgetToY F d))]
    {U U' : Over S} [IsAffine U.left] [IsAffine U'.left]
    (i : U ⟶ U') [IsFirstOrderThickening i.left]
    (y' : GroupoidsOver.slice U' ⟶ asGroupoidsOver 𝒴)
    (x : GroupoidsOver.slice U ⟶ asGroupoidsOver (lciStack F d))
    (γ : x ≫ asGroupoidsOverMor (lciForgetToY F d) ≅ slice.pullback i y') :
    ∃ (x' : GroupoidsOver.slice U' ⟶ asGroupoidsOver (lciStack F d))
      (β : slice.pullback i x' ≅ x)
      (γ' : x' ≫ asGroupoidsOverMor (lciForgetToY F d) ≅ y'),
      FormallySmoothOnObjects.restrictionSquare
        (asGroupoidsOverMor (lciForgetToY F d)) i β γ γ' :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
