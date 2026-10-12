/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap39.Lemma_39_17_3
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.RelationAction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Groupoid.RelationAction

export AlgebraicGeometry.GroupoidScheme.RelationAction
  (group
    group_X
    toTargetProduct_condition
    toTargetProduct
    toTargetProduct_fst
    toTargetProduct_snd
    hom_condition
    hom
    hom_left
    one_smul
    mul_smul
    modObj
    action
    action_X
    action_smul
    isPseudoTorsor)

/- Lemma 39.17.4: the stabilizer, base-changed to the product of the object scheme with
itself, acts on the arrow relation by composition and makes it a pseudo-torsor. -/
@[stacks 04Q2] #check (AlgebraicGeometry.GroupoidScheme.RelationAction.isPseudoTorsor :
  ∀ {S : Scheme.{u}} (Q : AlgebraicGeometry.GroupoidScheme S),
    Mod.IsPseudoTorsor (AlgebraicGeometry.GroupoidScheme.RelationAction.action Q))

end AlgebraicGeometry.Scheme.Groupoid.RelationAction
