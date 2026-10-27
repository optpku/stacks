/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Group
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeIsom.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Evaluation

/-!
# Automorphism group algebraic spaces of sections

For a morphism `x : U.toGroupoids ⟶ X` from an algebraic space into an algebraic
stack, the sheaf `Isom_X(x, x)` is represented by a group algebraic space
`autGroup x` over `U`.
-/

@[expose] public section

set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Limits Bicategory MonoidalCategory CartesianMonoidalCategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {U : AlgebraicSpace S} (x : U.toGroupoids ⟶ X)

/-- The algebraic space representing `Isom_X(x, x)`. -/
def autSpace : AlgebraicSpace S :=
  IsRepresentableByAlgebraicSpace.representingSpace (isRepresentableByAlgebraicSpace_relativeAut
    (baseProjection.{u + 1, u, u + 1} X) x)

/-- The chosen equivalence from `Isom_X(x, x)` to the groupoid fibration of
`autSpace x`. -/
def autEquiv :
    relativeAut (baseProjection.{u + 1, u, u + 1} X) x ≌
      (autSpace x).toGroupoids :=
  IsRepresentableByAlgebraicSpace.representingEquiv (isRepresentableByAlgebraicSpace_relativeAut
    (baseProjection.{u + 1, u, u + 1} X) x)

/-- The structure morphism `Isom_X(x, x) ⟶ U` of algebraic spaces. -/
def autHom : autSpace x ⟶ U :=
  toGroupoids.recover (autEquiv x) (Bicategory.Equivalence.id _)
    (fst (baseProjection.{u + 1, u, u + 1} X) x)

/-- `Isom_X(x, x)` as an object of `Over U`. -/
def autOver : Over U :=
  Over.mk (autHom x)

/-- The underlying algebraic space of `autOver x` is `autSpace x`. -/
theorem autOver_left : (autOver x).left = autSpace x := sorry

/-- The structure morphism of `autOver x` is `autHom x`. -/
theorem autOver_hom : (autOver x).hom = autHom x := sorry

/-- The unit of `Isom_X(x, x)`, recovered from `unitMap`. -/
def autOneLeft : U ⟶ autSpace x :=
  toGroupoids.recover (Bicategory.Equivalence.id _) (autEquiv x)
    (unitMap (baseProjection.{u + 1, u, u + 1} X) x)

/-- The identity section lies over the identity of the base. -/
private theorem Implementation.autOneHom_w :
    autOneLeft x ≫ (autOver x).hom = (𝟙_ (Over U)).hom := sorry

/-- The unit morphism of `autOver x` in `Over U`. -/
def autOneHom : 𝟙_ (Over U) ⟶ autOver x :=
  Over.homMk (autOneLeft x) (Implementation.autOneHom_w x)

/-- The underlying algebraic-space map of `autOneHom x` is `autOneLeft x`. -/
theorem autOneHom_left : (autOneHom x).left = autOneLeft x := sorry

/-- Inversion of `Isom_X(x, x)`, recovered from `invMap`. -/
def autInvLeft : autSpace x ⟶ autSpace x :=
  toGroupoids.recover (autEquiv x) (autEquiv x)
    (invMap (baseProjection.{u + 1, u, u + 1} X) x)

/-- Inversion preserves the structure morphism to the base. -/
private theorem Implementation.autInvHom_w :
    autInvLeft x ≫ (autOver x).hom = (autOver x).hom := sorry

/-- The inversion morphism of `autOver x` in `Over U`. -/
def autInvHom : autOver x ⟶ autOver x :=
  Over.homMk (autInvLeft x) (Implementation.autInvHom_w x)

/-- The underlying algebraic-space map of `autInvHom x` is `autInvLeft x`. -/
theorem autInvHom_left : (autInvHom x).left = autInvLeft x := sorry

/-- The first projection of the algebraic-space pullback of `autHom x`, as a
1-morphism of groupoid fibrations into `Isom_X(x, x)`. -/
private def autPullbackFst :
    (pullback (autHom x) (autHom x)).toGroupoids ⟶
      relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  toGroupoids.ofHom (Bicategory.Equivalence.id _) (autEquiv x)
    (pullback.fst (autHom x) (autHom x))

/-- The second projection of the algebraic-space pullback of `autHom x`, as a
1-morphism of groupoid fibrations into `Isom_X(x, x)`. -/
private def autPullbackSnd :
    (pullback (autHom x) (autHom x)).toGroupoids ⟶
      relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  toGroupoids.ofHom (Bicategory.Equivalence.id _) (autEquiv x)
    (pullback.snd (autHom x) (autHom x))

/-- First projection of the pullback, composed with `fst`, recovers
`pullback.fst ≫ autHom`. -/
private def autPullbackFst_comp_iso :
    autPullbackFst x ≫ fst (baseProjection.{u + 1, u, u + 1} X) x ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) (Bicategory.Equivalence.id _)
        (pullback.fst (autHom x) (autHom x) ≫ autHom x) :=
  α_ ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map (pullback.fst (autHom x) (autHom x)))
      (autEquiv x).inv (fst (baseProjection.{u + 1, u, u + 1} X) x) ≪≫
    whiskerLeftIso
      ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map (pullback.fst (autHom x) (autHom x)))
      ((Bicategory.rightUnitor
            ((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x)).symm ≪≫
        whiskerLeftIso ((autEquiv x).inv ≫
            fst (baseProjection.{u + 1, u, u + 1} X) x)
          (Bicategory.Equivalence.id _).unit ≪≫
        α_ ((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x)
          (Bicategory.Equivalence.id _).hom (Bicategory.Equivalence.id _).inv) ≪≫
    α_ ((Bicategory.Equivalence.id _).hom ≫
          toGroupoids.map (pullback.fst (autHom x) (autHom x)))
        (((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x) ≫
          (Bicategory.Equivalence.id _).hom)
        (Bicategory.Equivalence.id _).inv ≪≫
    whiskerRightIso
      (α_ (Bicategory.Equivalence.id _).hom
          (toGroupoids.map (pullback.fst (autHom x) (autHom x)))
          (((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x) ≫
            (Bicategory.Equivalence.id _).hom)).symm
      (Bicategory.Equivalence.id _).inv ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (whiskerLeftIso (toGroupoids.map (pullback.fst (autHom x) (autHom x)))
          (toGroupoids.evalMapIso ((autEquiv x).inv ≫
            fst (baseProjection.{u + 1, u, u + 1} X) x))))
      (Bicategory.Equivalence.id _).inv

/-- Second projection of the pullback, composed with `fst`, recovers
`pullback.snd ≫ autHom`. -/
private def autPullbackSnd_comp_iso :
    autPullbackSnd x ≫ fst (baseProjection.{u + 1, u, u + 1} X) x ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) (Bicategory.Equivalence.id _)
        (pullback.snd (autHom x) (autHom x) ≫ autHom x) :=
  α_ ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map (pullback.snd (autHom x) (autHom x)))
      (autEquiv x).inv (fst (baseProjection.{u + 1, u, u + 1} X) x) ≪≫
    whiskerLeftIso
      ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map (pullback.snd (autHom x) (autHom x)))
      ((Bicategory.rightUnitor
            ((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x)).symm ≪≫
        whiskerLeftIso ((autEquiv x).inv ≫
            fst (baseProjection.{u + 1, u, u + 1} X) x)
          (Bicategory.Equivalence.id _).unit ≪≫
        α_ ((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x)
          (Bicategory.Equivalence.id _).hom (Bicategory.Equivalence.id _).inv) ≪≫
    α_ ((Bicategory.Equivalence.id _).hom ≫
          toGroupoids.map (pullback.snd (autHom x) (autHom x)))
        (((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x) ≫
          (Bicategory.Equivalence.id _).hom)
        (Bicategory.Equivalence.id _).inv ≪≫
    whiskerRightIso
      (α_ (Bicategory.Equivalence.id _).hom
          (toGroupoids.map (pullback.snd (autHom x) (autHom x)))
          (((autEquiv x).inv ≫ fst (baseProjection.{u + 1, u, u + 1} X) x) ≫
            (Bicategory.Equivalence.id _).hom)).symm
      (Bicategory.Equivalence.id _).inv ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (whiskerLeftIso (toGroupoids.map (pullback.snd (autHom x) (autHom x)))
          (toGroupoids.evalMapIso ((autEquiv x).inv ≫
            fst (baseProjection.{u + 1, u, u + 1} X) x))))
      (Bicategory.Equivalence.id _).inv

/-- The two pullback projections become 2-isomorphic after composing with
`fst`, by the pullback condition. -/
private def autPullbackIso :
    autPullbackFst x ≫ fst (baseProjection.{u + 1, u, u + 1} X) x ≅
      autPullbackSnd x ≫ fst (baseProjection.{u + 1, u, u + 1} X) x :=
  autPullbackFst_comp_iso x ≪≫
    eqToIso
      (congrArg
        (toGroupoids.ofHom (Bicategory.Equivalence.id _)
          (Bicategory.Equivalence.id _))
        (pullback.condition :
          pullback.fst (autHom x) (autHom x) ≫ autHom x =
            pullback.snd (autHom x) (autHom x) ≫ autHom x)) ≪≫
    (autPullbackSnd_comp_iso x).symm

/-- The cone presenting the algebraic-space pullback of `autHom x` as a
2-fibre product of `fst` against itself. -/
private def autPullbackCone :
    Bicategory.PseudoPullbackCone
      (fst (baseProjection.{u + 1, u, u + 1} X) x)
      (fst (baseProjection.{u + 1, u, u + 1} X) x) where
  pt := (pullback (autHom x) (autHom x)).toGroupoids
  fst := autPullbackFst x
  snd := autPullbackSnd x
  iso := autPullbackIso x

/-- The comparison from the algebraic-space pullback of `autHom x` to
`(Isom_X(x, x)) ×_U (Isom_X(x, x))`. -/
private def autPullbackToPair :
    (pullback (autHom x) (autHom x)).toGroupoids ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        (fst (baseProjection.{u + 1, u, u + 1} X) x)
        (fst (baseProjection.{u + 1, u, u + 1} X) x) :=
  Bicategory.PseudoPullbackCone.lift (autPullbackCone x)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      (fst (baseProjection.{u + 1, u, u + 1} X) x)
      (fst (baseProjection.{u + 1, u, u + 1} X) x))

/-- Multiplication of `Isom_X(x, x)`, recovered from `mulMap`. -/
def autMulLeft : pullback (autHom x) (autHom x) ⟶ autSpace x :=
  toGroupoids.recover (Bicategory.Equivalence.id _) (autEquiv x)
    (autPullbackToPair x ≫ mulMap (baseProjection.{u + 1, u, u + 1} X) x)

/-- Multiplication preserves the structure morphism to the base. -/
private theorem Implementation.autMulHom_w :
    autMulLeft x ≫ (autOver x).hom = (autOver x ⊗ autOver x).hom := sorry

/-- The multiplication morphism of `autOver x` in `Over U`. -/
def autMulHom : autOver x ⊗ autOver x ⟶ autOver x :=
  Over.homMk (autMulLeft x) (Implementation.autMulHom_w x)

/-- The underlying algebraic-space map of `autMulHom x` is `autMulLeft x`. -/
theorem autMulHom_left : (autMulHom x).left = autMulLeft x := sorry

/-- The identity is a left unit for automorphism composition. -/
private theorem Implementation.autOne_mul :
    autOneHom x ▷ autOver x ≫ autMulHom x = (λ_ (autOver x)).hom := sorry

/-- The identity is a right unit for automorphism composition. -/
private theorem Implementation.autMul_one :
    autOver x ◁ autOneHom x ≫ autMulHom x = (ρ_ (autOver x)).hom := sorry

/-- Automorphism composition is associative. -/
private theorem Implementation.autMul_assoc :
    (autMulHom x ▷ autOver x) ≫ autMulHom x =
      (α_ (autOver x) (autOver x) (autOver x)).hom ≫
        (autOver x ◁ autMulHom x) ≫ autMulHom x := sorry

/-- Inversion is a left inverse for automorphism composition. -/
private theorem Implementation.autLeft_inv :
    lift (autInvHom x) (𝟙 (autOver x)) ≫ autMulHom x =
      toUnit (autOver x) ≫ autOneHom x := sorry

/-- Inversion is a right inverse for automorphism composition. -/
private theorem Implementation.autRight_inv :
    lift (𝟙 (autOver x)) (autInvHom x) ≫ autMulHom x =
      toUnit (autOver x) ≫ autOneHom x := sorry

/-- The pulled-back composition law makes `Isom_X(x, x)` a group object in
`Over U`. -/
instance instGrpObjAutOver : GrpObj (autOver x) where
  one := autOneHom x
  mul := autMulHom x
  inv := autInvHom x
  one_mul := Implementation.autOne_mul x
  mul_one := Implementation.autMul_one x
  mul_assoc := Implementation.autMul_assoc x
  left_inv := Implementation.autLeft_inv x
  right_inv := Implementation.autRight_inv x

/-- The group algebraic space `G = Isom_X(x, x)` over `U`. -/
def autGroup : GroupAlgebraicSpace U :=
  Grp.mk (autOver x)

/-- The underlying object of `autGroup x` in `Over U` is `autOver x`. -/
theorem autGroup_X : (autGroup x).X = autOver x := sorry

/-- The structure morphism of `autGroup x` is `autHom x`. -/
theorem autGroup_hom : (autGroup x).X.hom = autHom x := sorry

/-- `autGroup x` represents the sheaf `Isom_X(x, x)`. -/
theorem autGroup_spec :
    Nonempty
      (aut x ≌ (autGroup x).X.left.toGroupoids) := sorry

/-- The structure morphism of `autGroup x` is induced by `fst` of
`Isom_X(x, x)`. -/
theorem autGroup_aut :
    toGroupoids.InducesHom
      (fst (baseProjection.{u + 1, u, u + 1} X) x)
      (autEquiv x) (Bicategory.Equivalence.id _) (autGroup x).X.hom := sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
