module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.Faithful
import StacksCheckRecall

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

/- Lemma 95.18.3: the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` of stacks in
groupoids over `(Sch/S)_fppf` is faithful. -/
@[stacks 05XV] #check (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute.faithful :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d],
    (StackOver.Groupoids.Hom.toBasedFunctor
      (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute F d)).Faithful)

/- The forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` is faithful on fibre categories. -/
#check (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute.fiberwiseFaithful :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ) [NeZero d] (U : Over S),
    (StackOver.Groupoids.Hom.fiberFunctor
      (AlgebraicGeometry.FiniteHilbertStack.forgetToAbsolute F d) U).Faithful)

end AlgebraicGeometry.FiniteHilbertStack
