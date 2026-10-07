module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap101.Definition_101_5_3_Group
public import stacks_project.Chap101.Definition_101_5_3_Isom

/-!
# Automorphism group algebraic spaces of sections

For a morphism `x : U.toGroupoids ⟶ X` from an algebraic space into an algebraic
stack, the sheaf `Isom_X(x, x)` is represented by a group algebraic space
`autGroup x` over `U`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Limits Bicategory MonoidalCategory CartesianMonoidalCategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The identity fibration of `(Sch/S)_fppf` is an algebraic stack. -/
instance instAlgebraicStack_base {S : Scheme.{u}} :
    AlgebraicStack (base.{u + 1, u, u + 1} (Over S)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack.RelativeIsom

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
variable {U : AlgebraicSpace S} (x : U.toGroupoids ⟶ X)

/-- The algebraic space representing `Isom_X(x, x)`. -/
def autSpace : AlgebraicSpace S :=
  representingSpace (isRepresentableByAlgebraicSpace_relativeAut
    (baseProjection.{u + 1, u, u + 1} X) x)

/-- The chosen equivalence from `Isom_X(x, x)` to the groupoid fibration of
`autSpace x`. -/
def autEquiv :
    relativeAut (baseProjection.{u + 1, u, u + 1} X) x ≌
      (autSpace x).toGroupoids :=
  representingEquiv (isRepresentableByAlgebraicSpace_relativeAut
    (baseProjection.{u + 1, u, u + 1} X) x)

/-- The structure morphism `Isom_X(x, x) ⟶ U` of algebraic spaces. -/
def autHom : autSpace x ⟶ U :=
  toGroupoids.recover (autEquiv x) (Bicategory.Equivalence.id _)
    (fst (baseProjection.{u + 1, u, u + 1} X) x)

/-- `Isom_X(x, x)` as an object of `Over U`. -/
def autOver : Over U :=
  Over.mk (autHom x)

/-- The underlying algebraic space of `autOver x` is `autSpace x`. -/
theorem autOver_left : (autOver x).left = autSpace x :=
  sorry

/-- The structure morphism of `autOver x` is `autHom x`. -/
theorem autOver_hom : (autOver x).hom = autHom x :=
  sorry

/-- The unit of `Isom_X(x, x)`, recovered from `unitMap`. -/
def autOneLeft : U ⟶ autSpace x :=
  toGroupoids.recover (Bicategory.Equivalence.id _) (autEquiv x)
    (unitMap (baseProjection.{u + 1, u, u + 1} X) x)

/-- The unit morphism of `autOver x` in `Over U`. -/
def autOneHom : 𝟙_ (Over U) ⟶ autOver x :=
  Over.homMk (autOneLeft x) sorry

/-- The underlying algebraic-space map of `autOneHom x` is `autOneLeft x`. -/
theorem autOneHom_left : (autOneHom x).left = autOneLeft x :=
  sorry

/-- Inversion of `Isom_X(x, x)`, recovered from `invMap`. -/
def autInvLeft : autSpace x ⟶ autSpace x :=
  toGroupoids.recover (autEquiv x) (autEquiv x)
    (invMap (baseProjection.{u + 1, u, u + 1} X) x)

/-- The inversion morphism of `autOver x` in `Over U`. -/
def autInvHom : autOver x ⟶ autOver x :=
  Over.homMk (autInvLeft x) sorry

/-- The underlying algebraic-space map of `autInvHom x` is `autInvLeft x`. -/
theorem autInvHom_left : (autInvHom x).left = autInvLeft x :=
  sorry

/-- The first projection of the algebraic-space pullback of `autHom x`, as a
1-morphism of groupoid fibrations into `Isom_X(x, x)`. -/
def autPullbackFst :
    (pullback (autHom x) (autHom x)).toGroupoids ⟶
      relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  toGroupoids.ofHom (Bicategory.Equivalence.id _) (autEquiv x)
    (pullback.fst (autHom x) (autHom x))

/-- The second projection of the algebraic-space pullback of `autHom x`, as a
1-morphism of groupoid fibrations into `Isom_X(x, x)`. -/
def autPullbackSnd :
    (pullback (autHom x) (autHom x)).toGroupoids ⟶
      relativeAut (baseProjection.{u + 1, u, u + 1} X) x :=
  toGroupoids.ofHom (Bicategory.Equivalence.id _) (autEquiv x)
    (pullback.snd (autHom x) (autHom x))

/-- First projection of the pullback, composed with `fst`, recovers
`pullback.fst ≫ autHom`. -/
def autPullbackFst_comp_iso :
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
          (evalMapIso ((autEquiv x).inv ≫
            fst (baseProjection.{u + 1, u, u + 1} X) x))))
      (Bicategory.Equivalence.id _).inv

/-- Second projection of the pullback, composed with `fst`, recovers
`pullback.snd ≫ autHom`. -/
def autPullbackSnd_comp_iso :
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
          (evalMapIso ((autEquiv x).inv ≫
            fst (baseProjection.{u + 1, u, u + 1} X) x))))
      (Bicategory.Equivalence.id _).inv

/-- The two pullback projections become 2-isomorphic after composing with
`fst`, by the pullback condition. -/
def autPullbackIso :
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
def autPullbackCone :
    Bicategory.PseudoPullbackCone
      (fst (baseProjection.{u + 1, u, u + 1} X) x)
      (fst (baseProjection.{u + 1, u, u + 1} X) x) where
  pt := (pullback (autHom x) (autHom x)).toGroupoids
  fst := autPullbackFst x
  snd := autPullbackSnd x
  iso := autPullbackIso x

/-- The comparison from the algebraic-space pullback of `autHom x` to
`(Isom_X(x, x)) ×_U (Isom_X(x, x))`. -/
def autPullbackToPair :
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

/-- The multiplication morphism of `autOver x` in `Over U`. -/
def autMulHom : autOver x ⊗ autOver x ⟶ autOver x :=
  Over.homMk (autMulLeft x) sorry

/-- The underlying algebraic-space map of `autMulHom x` is `autMulLeft x`. -/
theorem autMulHom_left : (autMulHom x).left = autMulLeft x :=
  sorry

/-- The pulled-back composition law makes `Isom_X(x, x)` a group object in
`Over U`. -/
instance instGrpObj_autOver : GrpObj (autOver x) where
  one := autOneHom x
  mul := autMulHom x
  inv := autInvHom x
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  left_inv := sorry
  right_inv := sorry

/-- The group algebraic space `G = Isom_X(x, x)` over `U`. -/
def autGroup : GroupAlgebraicSpace U :=
  Grp.mk (autOver x)

/-- The underlying object of `autGroup x` in `Over U` is `autOver x`. -/
theorem autGroup_X : (autGroup x).X = autOver x :=
  sorry

/-- The structure morphism of `autGroup x` is `autHom x`. -/
theorem autGroup_hom : (autGroup x).X.hom = autHom x :=
  sorry

/-- `autGroup x` represents the sheaf `Isom_X(x, x)`. -/
theorem autGroup_spec :
    Nonempty
      (aut x ≌ (autGroup x).X.left.toGroupoids) :=
  sorry

/-- The structure morphism of `autGroup x` is induced by `fst` of
`Isom_X(x, x)`. -/
theorem autGroup_aut :
    toGroupoids.InducesHom
      (fst (baseProjection.{u + 1, u, u + 1} X) x)
      (autEquiv x) (Bicategory.Equivalence.id _) (autGroup x).X.hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack.RelativeIsom
