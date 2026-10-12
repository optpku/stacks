/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap98.Lemma_98_27_6_Solution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial bijections yield Artin contraction solutions

In Situation 98.27.1, an algebraic space locally of finite type over `S` that
agrees with the contraction functor on locally Noetherian schemes over `S` is a
solution.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.StandardTopology

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.6: In Situation 98.27.1, if an algebraic space `X` is locally of
finite type over `S` and there is a functorial bijection
`σ.functor V = Mor_S(V, X)` on locally Noetherian schemes `V` over `S`, then
`X` is a solution. -/
@[stacks 0GHC]
theorem nonempty_solutionFor_of_natIso (σ : ContractionSituation S)
    (X : AlgebraicSpace S) [LocallyOfFiniteType (toBase X)]
    (e : σ.functor ≅ homOnLocallyNoetherian X) :
    Nonempty (SolutionFor σ X) :=
  sorry

/-- The components of a natural isomorphism `σ.functor ≅ homOnLocallyNoetherian X`
are objectwise bijections from compatible triples on `V` to morphisms
`ofOver V ⟶ X`. -/
theorem natIso_app_bijective {σ : ContractionSituation S} {X : AlgebraicSpace S}
    [LocallyOfFiniteType (toBase X)]
    (e : σ.functor ≅ homOnLocallyNoetherian X)
    (V : (locallyNoetherian S).FullSubcategory) :
    Function.Bijective (fun ξ : Triple σ V.obj ↦ e.hom.app (op V) ξ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
