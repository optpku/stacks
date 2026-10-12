/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.«97_12_5_1»
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

/-!
# Lemma 97.12.5

If `F : 𝒳 ⟶ 𝒴` is a 1-morphism of stacks in groupoids over `(Sch/S)_fppf`
and the object diagonal of `𝒴` is representable by algebraic spaces, then the
forgetful pairing `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 95.18.2.1 is
representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.FiniteHilbertStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The forgetful pairing `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 95.18.2.1,
as the universal lift of `forgetToAbsolute F d` and `forgetToY F d` into the
2-fibre product of the two `baseProjection` morphisms. -/
noncomputable def forgetToProduct (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    asGroupoidsOver (stack (asGroupoidsOverMor F) d) ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)))
        (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)) :=
  pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d)) (asGroupoidsOverMor (forgetToY F d))

/-- `forgetToProduct` is `pairOverBase` of the two forgetful 1-morphisms of
Equation 95.18.2.1. -/
theorem forgetToProduct_eq (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToProduct F d =
      pairOverBase (asGroupoidsOverMor (forgetToAbsolute F d))
        (asGroupoidsOverMor (forgetToY F d)) :=
  sorry

/-- The first projection of `forgetToProduct F d` is isomorphic to
`asGroupoidsOverMor (forgetToAbsolute F d)`. -/
noncomputable def forgetToProduct_fst (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToProduct F d ≫
        TwoFibreProduct.fst.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)))
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)) ≅
      asGroupoidsOverMor (forgetToAbsolute F d) :=
  pairOverBase_fst (asGroupoidsOverMor (forgetToAbsolute F d))
    (asGroupoidsOverMor (forgetToY F d))

/-- The second projection of `forgetToProduct F d` is isomorphic to
`asGroupoidsOverMor (forgetToY F d)`. -/
noncomputable def forgetToProduct_snd (F : 𝒳 ⟶ 𝒴) (d : ℕ) :
    forgetToProduct F d ≫
        TwoFibreProduct.snd.{u + 1, u, u + 1, u}
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)))
          (baseProjection.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)) ≅
      asGroupoidsOverMor (forgetToY F d) :=
  pairOverBase_snd (asGroupoidsOverMor (forgetToAbsolute F d))
    (asGroupoidsOverMor (forgetToY F d))

/-- Lemma 97.12.5: Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over
`(Sch/S)_fppf`. If the object diagonal `Δ : 𝒴 ⟶ 𝒴 × 𝒴` is representable by
algebraic spaces, then the forgetful pairing
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳) × 𝒴` of Equation 95.18.2.1 is representable by algebraic
spaces. -/
@[stacks 05YH]
theorem forgetToProduct.relativelyRepresentableByAlgebraicSpaces (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (h_diagonal : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (asGroupoidsOver 𝒴))) :
    relativelyRepresentableByAlgebraicSpaces (forgetToProduct F d) :=
  sorry

/-- The displayed 2-fibre product
`(Sch/U)_fppf ×_{ξ × y, ℋ_d(𝒳) × 𝒴} ℋ_d(𝒳/𝒴)` is representable by an
algebraic space. -/
theorem relativeResIsom.isRepresentableByAlgebraicSpace (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    (h_diagonal : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} (asGroupoidsOver 𝒴)))
    {U : Over S} (ξ : (asGroupoidsOver (ofStack (asGroupoidsOver 𝒳) d)).p.Fiber U)
    (y : (asGroupoidsOver 𝒴).p.Fiber U) :
    IsRepresentableByAlgebraicSpace (relativeResIsom F d ξ y) :=
  sorry

end AlgebraicGeometry.FiniteHilbertStack
