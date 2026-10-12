/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Cartesian.ActionEquivalence
import StacksCheckRecall

universe u

/- Lemma 39.21.2: for a groupoid scheme `G` over `S`, groupoid schemes cartesian over `G`
are canonically equivalent to schemes `V` over `G.U` equipped with an isomorphism between
their target and source pullbacks satisfying the unit and cocycle laws. -/
@[stacks 0APE] #check
  (AlgebraicGeometry.GroupoidScheme.CartesianOver.cartesianActionEquivalence :
    {S : AlgebraicGeometry.Scheme.{u}} →
      (G : AlgebraicGeometry.GroupoidScheme S) →
        AlgebraicGeometry.GroupoidScheme.CartesianOver G ≌
          AlgebraicGeometry.GroupoidScheme.Action G)
