module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Comparison
import StacksCheckRecall

/-!
# Functorial bijections from Artin contraction solutions

In Situation 98.27.1, a solution induces a functorial bijection between
compatible triples and morphisms into `X` on locally Noetherian schemes over
`S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u


/- Lemma 98.27.5: In Situation 98.27.1, if there exists a solution
`(f : X' ⟶ X, T, a)`, then there is a functorial bijection
`σ.functor V = Mor_S(V, X)` on locally Noetherian schemes `V` over `S`.
The comparison `homOnLocallyNoetherian X ⟶ σ.functor` sends `x : V ⟶ X` to
the triple with `Z` the inverse image of `T`, `u'` the restriction of `x` to
`V \ Z` after identifying `U'` with `X \ T`, and `hatx = a ∘ x_/Z`. -/
@[stacks 0GHB]
#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.SolutionFor.isIso_ofHomNatTrans :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {σ : ContractionSituation S} {X : AlgebraicSpace S}
    (sol : ContractionSituation.SolutionFor σ X),
    IsIso sol.ofHomNatTrans)

#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.SolutionFor.tripleOfHom_bijective :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {σ : ContractionSituation S} {X : AlgebraicSpace S}
    (sol : ContractionSituation.SolutionFor σ X)
    (V : (locallyNoetherian S).FullSubcategory),
    Function.Bijective (fun x : ofOver V.obj ⟶ X ↦ sol.tripleOfHom x))

#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.SolutionFor.ofHomNatTrans :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    {σ : ContractionSituation S} {X : AlgebraicSpace S}
    (sol : ContractionSituation.SolutionFor σ X),
    homOnLocallyNoetherian X ⟶ σ.functor)
