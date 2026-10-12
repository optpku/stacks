/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap78.Lemma_78_16_1_Groupoid
import stacks_project.Chap78.Lemma_78_16_1_Stabilizer
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 78.16.1: the algebraic space G given by the pullback of j = (t, s)
along the diagonal is a group algebraic space over U, with multiplication
induced by groupoid composition. -/
@[stacks 0447] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizer :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CategoryTheory.Grp (CategoryTheory.Over G.U))

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizer_X :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.stabilizer.X = G.toPreRelation.stabilizer)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizer_mul :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.stabilizer.grp.mul = AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerMul G)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerMul_toArrows :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerMul G).left ≫
          G.toPreRelation.stabilizerToArrows =
        AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerComposablePair G ≫ G.c)
