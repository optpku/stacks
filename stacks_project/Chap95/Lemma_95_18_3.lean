module

public import stacks_project.Chap95.«95_18_2_1_Forgetful»

/-!
# Lemma 95.18.3

The forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` of stacks in groupoids over
`(Sch/S)_fppf` is faithful for `d ≥ 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- Lemma 95.18.3: the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` of stacks in
groupoids over `(Sch/S)_fppf` is faithful. -/
@[stacks 05XV]
instance forgetToAbsolute.faithful (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d] :
    (toBasedFunctor (forgetToAbsolute F d)).Faithful := sorry

/-- The forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is faithful on fibre categories. -/
theorem forgetToAbsolute.fiberwiseFaithful (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d] (U : Over S) :
    (fiberFunctor (forgetToAbsolute F d) U).Faithful := sorry

end AlgebraicGeometry.FiniteHilbertStack
