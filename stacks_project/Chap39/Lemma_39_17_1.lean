/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 39.17.1: the pullback of a groupoid scheme along the diagonal is a group scheme
over its object scheme, with multiplication induced by groupoid composition. -/
@[stacks 0235] #check
  (AlgebraicGeometry.GroupoidScheme.stabilizer :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      CategoryTheory.Grp (CategoryTheory.Over G.U))

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizer_X :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.stabilizer.X = G.toPreRelation.stabilizer)

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizer_mul :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.stabilizer.grp.mul = AlgebraicGeometry.GroupoidScheme.stabilizerMul G)

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizerMul_toArrows :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.stabilizerMul G).left ≫
          G.toPreRelation.stabilizerToArrows =
        AlgebraicGeometry.GroupoidScheme.stabilizerComposablePair G ≫ G.c)
