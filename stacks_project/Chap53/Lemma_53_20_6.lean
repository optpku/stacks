/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AtWorstNodal

/- Lemma 53.20.6: If `f : X ⟶ S` is at worst nodal of relative dimension one and
`e : Y ⟶ X` is étale, then `e ≫ f` is at worst nodal of relative dimension one. -/
@[stacks 0C5C] #check
  (AlgebraicGeometry.AtWorstNodal.etaleComp :
    ∀ {Y X S : AlgebraicGeometry.Scheme.{u}} (e : Y ⟶ X) (f : X ⟶ S)
      [AlgebraicGeometry.Etale e] [AlgebraicGeometry.AtWorstNodal f],
      AlgebraicGeometry.AtWorstNodal (e ≫ f))

end AlgebraicGeometry.AtWorstNodal
