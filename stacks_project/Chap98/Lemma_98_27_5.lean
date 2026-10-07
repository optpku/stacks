module

public import stacks_project.Chap98.Lemma_98_27_5_Comparison
import Mathlib.Tactic.CrossRefAttribute

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

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

namespace SolutionFor

variable {σ : ContractionSituation S} {X : AlgebraicSpace S}
  [LocallyOfFiniteType (toBase X)]

/-- Lemma 98.27.5: In Situation 98.27.1, if there exists a solution
`(f : X' ⟶ X, T, a)`, then there is a functorial bijection
`σ.functor V = Mor_S(V, X)` on locally Noetherian schemes `V` over `S`.
The comparison `homOnLocallyNoetherian X ⟶ σ.functor` sends `x : V ⟶ X` to
the triple with `Z` the inverse image of `T`, `u'` the restriction of `x` to
`V \ Z` after identifying `U'` with `X \ T`, and `hatx = a ∘ x_/Z`. -/
@[stacks 0GHB, instance]
instance instIsIso_ofHomNatTrans (sol : SolutionFor σ X) :
    IsIso sol.ofHomNatTrans :=
  sorry

/-- The comparison `Mor_S(V, X) → F(V)` is bijective on each locally Noetherian
scheme `V` over `S`. -/
theorem tripleOfHom_bijective (sol : SolutionFor σ X)
    (V : (locallyNoetherian S).FullSubcategory) :
    Function.Bijective (fun x : ofOver V.obj ⟶ X ↦ sol.tripleOfHom x) :=
  sorry

end SolutionFor

end ContractionSituation

end AlgebraicGeometry.AlgebraicSpace
