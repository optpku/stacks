/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.StabilizerAction
import StacksCheckRecall

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 78.16.3: the stabilizer group algebraic space of a groupoid in algebraic
spaces acts canonically on the arrow space over the target, with action induced by
groupoid composition. -/
@[stacks 0449] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerAction :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      Mod (Over G.U) G.stabilizer.X)

#check
  (GroupoidAlgebraicSpace.stabilizerAction_X :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (GroupoidAlgebraicSpace.stabilizerAction G).X =
        GroupoidAlgebraicSpace.arrowsOverTarget G)

#check
  (GroupoidAlgebraicSpace.stabilizerAction_smul :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (GroupoidAlgebraicSpace.stabilizerAction G).mod.smul =
        GroupoidAlgebraicSpace.actionHom G)

#check
  (GroupoidAlgebraicSpace.actionHom_left :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      (GroupoidAlgebraicSpace.actionHom G).left =
        GroupoidAlgebraicSpace.actionPair G ≫ G.c)
