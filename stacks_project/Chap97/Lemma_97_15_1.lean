module

public import ReasLib.AlgebraicGeometry.FiniteHilbertStack.LciOpenImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.FiniteHilbertStack
open scoped Bicategory

universe u

/- Lemma 97.15.1: Let `S` be a scheme. Fix a 1-morphism `F : 𝒳 ⟶ 𝒴`
of stacks in groupoids over `(Sch/S)_fppf`. Assume `F` is representable by
algebraic spaces, flat, and locally of finite presentation. Then
`H_{d,lci}(𝒳/𝒴)` is a stack in groupoids and the inclusion functor
`H_{d,lci}(𝒳/𝒴) ⟶ H_d(𝒳/𝒴)` is representable and an open immersion. -/
@[stacks 06CL]
#check (AlgebraicGeometry.FiniteHilbertStack.lciInclusion.openImmersion :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴) (d : ℕ)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)],
    Groupoids.Hom.OpenImmersion (asGroupoidsOverMor (lciInclusion F d)))

#check (AlgebraicGeometry.FiniteHilbertStack.lciP_isStack :
  ∀ {S : Scheme.{u}}
    {𝒳 𝒴 : StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}
    (F : 𝒳 ⟶ 𝒴)
    [Groupoids.Hom.Flat (asGroupoidsOverMor F)]
    [Groupoids.Hom.LocallyOfFinitePresentation (asGroupoidsOverMor F)] (d : ℕ),
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (lciP F d))
