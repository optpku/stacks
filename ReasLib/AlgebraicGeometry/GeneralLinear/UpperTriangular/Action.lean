/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GeneralLinear.UpperTriangular
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Action

/-!
# The inverse-right action of the upper-triangular subgroup on `GL₂`

This file constructs the action groupoid presenting right upper-triangular cosets in `GL₂`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GLTwo.UpperTriangular

/-- The inverse-right action map `(b, g) ↦ g · inclusion(b)⁻¹`. -/
def rightActionHom (k : Type u) [CommRing k] :
    (groupScheme k).X ⊗ (GeneralLinear.groupScheme k (GLTwo.index)).X ⟶
      (GeneralLinear.groupScheme k (GLTwo.index)).X :=
  lift
      (snd (groupScheme k).X (GeneralLinear.groupScheme k (GLTwo.index)).X)
      (fst (groupScheme k).X (GeneralLinear.groupScheme k (GLTwo.index)).X ≫
        inclusion k ≫ ι[GeneralLinear.schemeOver k (GLTwo.index)]) ≫
    μ[GeneralLinear.schemeOver k (GLTwo.index)]

/-- The inverse-right action satisfies the identity-action law. -/
theorem rightActionHom_one_smul (k : Type u) [CommRing k] :
    η[(groupScheme k).X] ⊵ₗ (GeneralLinear.groupScheme k (GLTwo.index)).X ≫
        rightActionHom k =
      (λₗ (GeneralLinear.groupScheme k (GLTwo.index)).X).hom := sorry

/-- The inverse-right action is compatible with multiplication in the acting group. -/
theorem rightActionHom_mul_smul (k : Type u) [CommRing k] :
    μ[(groupScheme k).X] ⊵ₗ (GeneralLinear.groupScheme k (GLTwo.index)).X ≫
        rightActionHom k =
      (αₗ (groupScheme k).X (groupScheme k).X
          (GeneralLinear.groupScheme k (GLTwo.index)).X).hom ≫
        (groupScheme k).X ⊴ₗ rightActionHom k ≫ rightActionHom k := sorry

/-- The inverse-right module-object structure, kept explicit because `GL₂` also admits
other actions of the upper-triangular group. -/
def instModObjRightAction (k : Type u) [CommRing k] :
    ModObj (groupScheme k).X (GeneralLinear.groupScheme k (GLTwo.index)).X where
  smul := rightActionHom k
  one_smul := rightActionHom_one_smul k
  mul_smul := rightActionHom_mul_smul k

/-- The inverse-right action of the upper-triangular group scheme on `GL₂`. -/
def rightAction (k : Type u) [CommRing k] :
    Mod (Over (Spec (CommRingCat.of k))) (groupScheme k).X where
  X := (GeneralLinear.groupScheme k (GLTwo.index)).X
  mod := instModObjRightAction k

/-- The generalized-point formula for the inverse-right action. -/
theorem rightAction_smul (k : Type u) [CommRing k] :
    (rightAction k).mod.smul = rightActionHom k := rfl

/-- The action groupoid presenting right upper-triangular cosets in `GL₂`. -/
def relation (k : Type u) [CommRing k] : GroupoidScheme (Spec (CommRingCat.of k)) :=
  GroupoidScheme.ofAction (groupScheme k) (rightAction k)

/-- The object scheme of `relation k` is `GL₂`. -/
theorem relation_U (k : Type u) [CommRing k] :
    (relation k).U = (GeneralLinear.groupScheme k (GLTwo.index)).X := sorry

/-- The arrow scheme of `relation k` is `B ×ₖ GL₂`. -/
theorem relation_R (k : Type u) [CommRing k] :
    (relation k).R =
      (groupScheme k).X ⊗ (GeneralLinear.groupScheme k (GLTwo.index)).X := sorry

/-- The arrow scheme in action-groupoid order is canonically isomorphic to `GL₂ ×ₖ B`. -/
def arrowsIso (k : Type u) [CommRing k] :
    (relation k).R ≅
      (GeneralLinear.groupScheme k (GLTwo.index)).X ⊗ (groupScheme k).X :=
  β_ (groupScheme k).X (GeneralLinear.groupScheme k (GLTwo.index)).X

/-- The source map of the action groupoid is projection to `GL₂`. -/
theorem relation_s (k : Type u) [CommRing k] :
    (relation k).s = GroupoidScheme.actionSource (groupScheme k) (rightAction k) := sorry

/-- The target map of the action groupoid is the inverse-right action. -/
theorem relation_t (k : Type u) [CommRing k] :
    (relation k).t = GroupoidScheme.actionTarget (groupScheme k) (rightAction k) := sorry

end AlgebraicGeometry.GLTwo.UpperTriangular
