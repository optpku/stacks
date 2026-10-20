/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Representability
import StacksCheckRecall

/-!
# Functorial bijections yield Artin contraction solutions

In Situation 98.27.1, an algebraic space locally of finite type over `S` that
agrees with the contraction functor on locally Noetherian schemes over `S` is a
solution.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 98.27.6: In Situation 98.27.1, if an algebraic space `X` is locally of
finite type over `S` and there is a functorial bijection
`σ.functor V = Mor_S(V, X)` on locally Noetherian schemes `V` over `S`, then
`X` is a solution. -/
@[stacks 0GHC] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.nonempty_solutionFor_of_natIso :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S) (X : AlgebraicSpace S)
      [AlgebraicSpace.LocallyOfFiniteType (SchemeRealization.toBase X)]
      (e : σ.functor ≅ homOnLocallyNoetherian X),
      Nonempty (ContractionSituation.SolutionFor σ X))
