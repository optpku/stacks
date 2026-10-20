/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap39.Definition_39_17_2_Stabilizer
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Action
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Groupoid

export AlgebraicGeometry.GroupoidScheme
  (arrowsOverTarget
    arrowsOverTarget_hom
    actionFirst
    actionSecond
    actionPair_condition
    actionPair
    actionPair_fst
    actionPair_snd
    actionHom_condition
    actionHom
    actionHom_left
    actionHom_one_smul
    actionHom_mul_smul
    actionModObj
    stabilizerAction
    stabilizerAction_X
    stabilizerAction_smul)

/- Lemma 39.17.3: the stabilizer group scheme of a groupoid scheme acts canonically on
the arrow scheme over the target, with action induced by groupoid composition. -/
@[stacks 0237] #check
  (AlgebraicGeometry.GroupoidScheme.stabilizerAction :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      Mod (Over G.U) G.stabilizer.X)

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizerAction_X :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.stabilizerAction G).X =
        AlgebraicGeometry.GroupoidScheme.arrowsOverTarget G)

#check
  (AlgebraicGeometry.GroupoidScheme.stabilizerAction_smul :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.stabilizerAction G).mod.smul =
        AlgebraicGeometry.GroupoidScheme.actionHom G)

#check
  (AlgebraicGeometry.GroupoidScheme.actionHom_left :
    ∀ {S : Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.actionHom G).left =
        AlgebraicGeometry.GroupoidScheme.actionPair G ≫ G.c)

end AlgebraicGeometry.Scheme.Groupoid
