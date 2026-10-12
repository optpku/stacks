/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Stabilizer.Action
public import ReasLib.CategoryTheory.Monoidal.Cartesian.PseudoTorsor

/-!
# The stabilizer action on the relation of a groupoid scheme

The stabilizer, base-changed to the product of the object scheme with itself, acts on the
arrow relation by groupoid composition. This action is a pseudo-torsor.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme.RelationAction

variable {S : Scheme.{u}} (Q : GroupoidScheme S)

/-- The stabilizer group of `Q`, base-changed to `Q.U ⨯ Q.U` along the first projection. -/
def group : Grp (Over (Q.U ⨯ Q.U)) :=
  (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)).mapGrp.obj Q.stabilizer

/-- The object of `group Q` is the pullback of the stabilizer along the first projection. -/
theorem group_X :
    (group Q).X =
      (Over.pullback (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)).obj Q.stabilizer.X := sorry

/-- The pulled-back stabilizer component and the arrow component have the same target. -/
theorem toTargetProduct_condition :
    ((fst (group Q).X Q.toPreRelation).left ≫
        pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U)) ≫
          Q.stabilizer.X.hom =
      (snd (group Q).X Q.toPreRelation).left ≫ Q.t := sorry

/-- The canonical map from the pulled-back action product to the stabilizer action product. -/
def toTargetProduct :
    ((group Q).X ⊗ Q.toPreRelation).left ⟶
      (Q.stabilizer.X ⊗ Q.arrowsOverTarget).left :=
  pullback.lift
    ((fst (group Q).X Q.toPreRelation).left ≫
      pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U))
    (snd (group Q).X Q.toPreRelation).left (toTargetProduct_condition Q)

/-- The first projection of `toTargetProduct Q` is the pulled-back stabilizer element. -/
theorem toTargetProduct_fst :
    toTargetProduct Q ≫ pullback.fst Q.stabilizer.X.hom Q.t =
      (fst (group Q).X Q.toPreRelation).left ≫
        pullback.fst Q.stabilizer.X.hom (prod.fst : Q.U ⨯ Q.U ⟶ Q.U) := sorry

/-- The second projection of `toTargetProduct Q` is the arrow being acted upon. -/
theorem toTargetProduct_snd :
    toTargetProduct Q ≫ pullback.snd Q.stabilizer.X.hom Q.t =
      (snd (group Q).X Q.toPreRelation).left := sorry

/-- Composition with the pulled-back stabilizer preserves the target-source pair. -/
theorem hom_condition :
    (toTargetProduct Q ≫ (actionHom Q).left) ≫ Q.toPreRelation.hom =
      ((group Q).X ⊗ Q.toPreRelation).hom := sorry

/-- The action morphism over `Q.U ⨯ Q.U` induced by groupoid composition. -/
def hom : (group Q).X ⊗ Q.toPreRelation ⟶ Q.toPreRelation :=
  Over.homMk (toTargetProduct Q ≫ (actionHom Q).left) (hom_condition Q)

/-- The underlying morphism of `hom Q` is induced by `actionHom Q`. -/
theorem hom_left :
    (hom Q).left = toTargetProduct Q ≫ (actionHom Q).left := sorry

/-- The induced action satisfies the identity-action law. -/
theorem one_smul :
    η[(group Q).X] ⊵ₗ Q.toPreRelation ≫ hom Q =
      (λₗ Q.toPreRelation).hom := sorry

/-- The induced action is compatible with multiplication in `group Q`. -/
theorem mul_smul :
    μ[(group Q).X] ⊵ₗ Q.toPreRelation ≫ hom Q =
      (αₗ (group Q).X (group Q).X Q.toPreRelation).hom ≫
        (group Q).X ⊴ₗ hom Q ≫ hom Q := sorry

/-- The module-object structure on the arrow scheme over `Q.U ⨯ Q.U`. -/
@[reducible]
def modObj : ModObj (group Q).X Q.toPreRelation where
  smul := hom Q
  one_smul := one_smul Q
  mul_smul := mul_smul Q

/-- The action of the base-changed stabilizer on the arrow scheme over `Q.U ⨯ Q.U`. -/
def action : Mod (Over (Q.U ⨯ Q.U)) (group Q).X where
  X := Q.toPreRelation
  mod := modObj Q

/-- The object acted on by `action Q` is exactly the arrow scheme over `Q.U ⨯ Q.U`. -/
theorem action_X :
    (action Q).X = Q.toPreRelation := sorry

/-- The action morphism stored by `action Q` is `hom Q`. -/
theorem action_smul :
    (action Q).mod.smul = hom Q := sorry

/-- The relation of a groupoid scheme is a pseudo-torsor under its base-changed stabilizer. -/
theorem isPseudoTorsor : Mod.IsPseudoTorsor (action Q) := sorry

end AlgebraicGeometry.GroupoidScheme.RelationAction
