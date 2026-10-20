/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous.Adjoint
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousLeftAdjoint
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.AffineIndEtaleClosedImmersion

/-!
# Affine closed immersions as morphisms of affine ind-étale topoi

A closed immersion of affine schemes induces the morphism of topoi associated
to the fully faithful cocontinuous lift `v : AffineIndEtale Z ⥤ AffineIndEtale X`.
Inverse image is sheafification of precomposition with `v`.
-/

public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

namespace AffineIndEtale

/-- The morphism of affine ind-étale topoi associated to the fully faithful
cocontinuous lift `v` of a closed immersion of affine schemes. -/
@[expose] def morphismOfTopoi (i : Z ⟶ X) [IsClosedImmersion i] :
    MorphismOfTopoiIn (affineIndEtaleTopology X) (affineIndEtaleTopology Z) :=
  (AffineIndEtale.lift i).morphismOfTopoiInOfCocontinuous
    (affineIndEtaleTopology Z) (affineIndEtaleTopology X)

/-- The morphism associated to `v` is the cocontinuous morphism of topoi of
affine ind-étale lift. -/
theorem morphismOfTopoi_def (i : Z ⟶ X) [IsClosedImmersion i] :
    morphismOfTopoi i =
      (AffineIndEtale.lift i).morphismOfTopoiInOfCocontinuous
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  rfl

/-- Inverse image of the morphism associated to `v` is cocontinuous sheaf
pullback along affine ind-étale lift. -/
theorem morphismOfTopoi_inverseImage (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (morphismOfTopoi i).inverseImage =
      (AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  rfl

/-- Direct image of the morphism associated to `v` is cocontinuous sheaf
pushforward along affine ind-étale lift. -/
theorem morphismOfTopoi_pushforward (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (morphismOfTopoi i).pushforward =
      (AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  rfl

/-- Inverse image along the continuous functor `u` agrees with inverse image
of the morphism of topoi associated to `v`. -/
@[expose] def morphismOfTopoi_eq_ofContinuous (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (AffineIndEtale.baseChange i).sheafPullback (Type (u + 1))
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      (morphismOfTopoi i).inverseImage :=
  Functor.CocontinuousLeftAdjoint.pullbackIsoInverseImage.{u + 1}
    (AffineIndEtale.baseChange i) (AffineIndEtale.lift i)
    (AffineIndEtale.liftAdjunction i)

/-- The comparison of inverse images is the cocontinuous-left-adjoint
identification of sheaf pullback along `u` with inverse image along `v`. -/
theorem morphismOfTopoi_eq_ofContinuous_def (i : Z ⟶ X)
    [IsClosedImmersion i] :
    morphismOfTopoi_eq_ofContinuous i =
      Functor.CocontinuousLeftAdjoint.pullbackIsoInverseImage.{u + 1}
        (AffineIndEtale.baseChange i) (AffineIndEtale.lift i)
        (AffineIndEtale.liftAdjunction i) :=
  rfl

/-- Continuous direct image along `u` agrees with cocontinuous direct image
along `v`. -/
@[expose] def morphismOfTopoi_pushforwardIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [HasLimitsOfSize.{u, u + 1} A] :
    (AffineIndEtale.baseChange i).sheafPushforwardContinuous A
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      (AffineIndEtale.lift i).sheafPushforwardCocontinuous A
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (AffineIndEtale.lift i) (AffineIndEtale.baseChange i) A
    (AffineIndEtale.liftAdjunction i)

/-- Inverse image of a type-valued sheaf along `v` is the sheaf associated to
the presheaf `V ↦ F(v(V))`. -/
theorem inverseImage_sheafify (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1))) :
    ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
          (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj F =
      (presheafToSheaf (affineIndEtaleTopology Z) (Type (u + 1))).obj
        ((AffineIndEtale.lift i).op ⋙ F.obj) :=
  rfl

/-- The canonical comparison from `F(v(V))` to the sections of the sheafified
presheaf `V ↦ F(v(V))`. -/
@[expose] def inverseImage_obj_to (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (V : AffineIndEtale Z) :
    F.obj.obj (op ((AffineIndEtale.lift i).obj V)) ⟶
      (((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
            (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj F).obj.obj
        (op V) :=
  ((sheafificationAdjunction (affineIndEtaleTopology Z) (Type (u + 1))).unit.app
      ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V)

/-- The comparison `inverseImage_obj_to` is the sheafification unit at `v(V)`. -/
theorem inverseImage_obj_to_app (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (V : AffineIndEtale Z) :
    inverseImage_obj_to i F V =
      ((sheafificationAdjunction (affineIndEtaleTopology Z) (Type (u + 1))).unit.app
          ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V) :=
  rfl

/-- On a weakly contractible affine ind-étale object, the sheafification unit
identifies `i⁻¹ F(V)` with `F(v(V))`. -/
instance inverseImage_obj_to_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso (inverseImage_obj_to i F V) :=
  sorry

/-- Abelian inverse image on affine ind-étale sites along `v`, as sheafification
of precomposition. -/
@[expose] def abelianInverseImage (i : Z ⟶ X) [IsClosedImmersion i] :
    Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1} :=
  (AffineIndEtale.lift i).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
    (affineIndEtaleTopology Z) (affineIndEtaleTopology X)

/-- Abelian inverse image is cocontinuous sheaf pullback along affine ind-étale
lift. -/
theorem abelianInverseImage_def (i : Z ⟶ X)
    [IsClosedImmersion i] :
    abelianInverseImage i =
      (AffineIndEtale.lift i).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  rfl

/-- Abelian inverse image of a sheaf along `v` is the sheaf associated to the
presheaf `V ↦ F(v(V))`. -/
theorem abelianInverseImage_sheafify (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (abelianInverseImage i).obj F =
      (presheafToSheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}).obj
        ((AffineIndEtale.lift i).op ⋙ F.obj) :=
  rfl

/-- The canonical comparison from `F(v(V))` to the sections of abelian inverse
image along `v`. -/
@[expose] def abelianInverseImage_obj_to (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (V : AffineIndEtale Z) :
    F.obj.obj (op ((AffineIndEtale.lift i).obj V)) ⟶
      ((abelianInverseImage i).obj F).obj.obj (op V) :=
  ((sheafificationAdjunction (affineIndEtaleTopology Z)
      AddCommGrpCat.{u + 1}).unit.app
    ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V)

/-- The abelian comparison `abelianInverseImage_obj_to` is the sheafification
unit at `v(V)`. -/
theorem abelianInverseImage_obj_to_app (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (V : AffineIndEtale Z) :
    abelianInverseImage_obj_to i F V =
      ((sheafificationAdjunction (affineIndEtaleTopology Z)
          AddCommGrpCat.{u + 1}).unit.app
        ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V) :=
  rfl

/-- Affine ind-étale inclusion followed by small pro-étale pullback is
continuous. -/
instance inclusion_comp_smallProetalePullback_isContinuous
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (affineIndEtaleInclusion X ⋙ smallProetalePullback i).IsContinuous
      (affineIndEtaleTopology X) (topology Z) :=
  Functor.isContinuous_comp (affineIndEtaleInclusion X) (smallProetalePullback i)
    (affineIndEtaleTopology X) (topology X) (topology Z)

/-- Affine ind-étale base change followed by inclusion is continuous. -/
instance baseChange_comp_inclusion_isContinuous
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (AffineIndEtale.baseChange i ⋙ affineIndEtaleInclusion Z).IsContinuous
      (affineIndEtaleTopology X) (topology Z) :=
  Functor.isContinuous_comp (AffineIndEtale.baseChange i) (affineIndEtaleInclusion Z)
    (affineIndEtaleTopology X) (affineIndEtaleTopology Z) (topology Z)

/-- Direct-image comparison of the affine/small base-change square. -/
private def smallInverseImage_restrictionIso_pushforward (i : Z ⟶ X)
    [IsClosedImmersion i]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [HasLimitsOfSize.{u, u + 1} A] [HasColimitsOfSize.{u, u + 1} A]
    [HasSheafify (topology X) A] [HasSheafify (topology Z) A]
    [HasSheafify (affineIndEtaleTopology X) A]
    [HasSheafify (affineIndEtaleTopology Z) A] :
    (smallProetalePullback i).sheafPushforwardContinuous A
        (topology X) (topology Z) ⋙
      ((affineIndEtaleInclusion X).sheafPushforwardContinuous A
        (affineIndEtaleTopology X) (topology X)) ≅
      ((affineIndEtaleInclusion Z).sheafPushforwardContinuous A
        (affineIndEtaleTopology Z) (topology Z)) ⋙
        (AffineIndEtale.baseChange i).sheafPushforwardContinuous A
          (affineIndEtaleTopology X) (affineIndEtaleTopology Z) :=
  (affineIndEtaleInclusion X).sheafPushforwardContinuousComp'
      (Iso.refl (affineIndEtaleInclusion X ⋙ smallProetalePullback i))
      A (affineIndEtaleTopology X) (topology X) (topology Z) ≪≫
    (Functor.sheafPushforwardContinuousIso (baseChange_comp_inclusion i).symm
      A (affineIndEtaleTopology X) (topology Z)) ≪≫
    ((AffineIndEtale.baseChange i).sheafPushforwardContinuousComp'
      (Iso.refl (AffineIndEtale.baseChange i ⋙ affineIndEtaleInclusion Z))
      A (affineIndEtaleTopology X) (affineIndEtaleTopology Z)
      (topology Z)).symm

/-- Mate of the affine/small pushforward comparison along the continuous
sheaf adjunctions of `u` and of small pro-étale pullback. -/
private def smallInverseImage_restrictionIso_mate (i : Z ⟶ X)
    [IsClosedImmersion i]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [HasLimitsOfSize.{u, u + 1} A] [HasColimitsOfSize.{u, u + 1} A]
    [HasSheafify (topology X) A] [HasSheafify (topology Z) A]
    [HasSheafify (affineIndEtaleTopology X) A]
    [HasSheafify (affineIndEtaleTopology Z) A] :
    ((affineIndEtaleInclusion X).sheafPushforwardContinuous A
        (affineIndEtaleTopology X) (topology X)) ⋙
        (AffineIndEtale.baseChange i).sheafPullback A
          (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ⟶
      (smallProetalePullback i).sheafPullback A
          (topology X) (topology Z) ⋙
        ((affineIndEtaleInclusion Z).sheafPushforwardContinuous A
        (affineIndEtaleTopology Z) (topology Z)) :=
  (mateEquiv
      ((smallProetalePullback i).sheafAdjunctionContinuous A
        (topology X) (topology Z))
      ((AffineIndEtale.baseChange i).sheafAdjunctionContinuous
        A (affineIndEtaleTopology X)
        (affineIndEtaleTopology Z))).symm
    (TwoSquare.mk _ _ _ _
      (smallInverseImage_restrictionIso_pushforward i A).hom)

/-- The affine/small inverse-image mate is the mate of the pushforward
comparison 2-cell. -/
private theorem smallInverseImage_restrictionIso_mate_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [HasLimitsOfSize.{u, u + 1} A] [HasColimitsOfSize.{u, u + 1} A]
    [HasSheafify (topology X) A] [HasSheafify (topology Z) A]
    [HasSheafify (affineIndEtaleTopology X) A]
    [HasSheafify (affineIndEtaleTopology Z) A] :
    smallInverseImage_restrictionIso_mate i A =
      (mateEquiv
          ((smallProetalePullback i).sheafAdjunctionContinuous A
            (topology X) (topology Z))
          ((AffineIndEtale.baseChange i).sheafAdjunctionContinuous
            A (affineIndEtaleTopology X)
            (affineIndEtaleTopology Z))).symm
        (TwoSquare.mk _ _ _ _
          (smallInverseImage_restrictionIso_pushforward i A).hom) :=
  rfl

/-- The affine/small inverse-image mate is an isomorphism. -/
private instance smallInverseImage_restrictionIso_mate_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [HasLimitsOfSize.{u, u + 1} A] [HasColimitsOfSize.{u, u + 1} A]
    [HasSheafify (topology X) A] [HasSheafify (topology Z) A]
    [HasSheafify (affineIndEtaleTopology X) A]
    [HasSheafify (affineIndEtaleTopology Z) A] :
    IsIso (smallInverseImage_restrictionIso_mate i A) :=
  sorry

/-- Inverse image along `i_proétale` on small pro-étale sites, after restriction
to affine ind-étale objects, agrees with inverse image along `v`. -/
def smallInverseImage_restrictionIso (i : Z ⟶ X)
    [IsClosedImmersion i] :
    affineIndEtaleRestriction X ⋙ (morphismOfTopoi i).inverseImage ≅
      (smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z := by
  exact
    Functor.isoWhiskerLeft (affineIndEtaleRestriction X)
        (morphismOfTopoi_eq_ofContinuous i).symm ≪≫
      (@asIso _ _ _ _ (smallInverseImage_restrictionIso_mate i (Type (u + 1)))
        (smallInverseImage_restrictionIso_mate_isIso i (Type (u + 1))))

/-- The small-site comparison is an isomorphism of inverse-image functors after
affine ind-étale restriction. -/
@[expose] def smallInverseImage_restrictionIso_app (i : Z ⟶ X)
    [IsClosedImmersion i]
    (F : Sheaf (topology X) (Type (u + 1))) :
    (affineIndEtaleRestriction X ⋙ (morphismOfTopoi i).inverseImage).obj F ≅
      ((smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z).obj F :=
  (smallInverseImage_restrictionIso i).app F

/-- Abelian inverse image along affine base change agrees with sheafified
precomposition along its left adjoint. -/
@[expose] def abelianInverseImage_eq_ofContinuous (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (AffineIndEtale.baseChange i).sheafPullback AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      abelianInverseImage i :=
  Functor.LeftAdjoint.pullbackIsoCocontinuous
    (AffineIndEtale.baseChange i) (AffineIndEtale.lift i)
    (AffineIndEtale.liftAdjunction i) AddCommGrpCat.{u + 1}

/-- Abelian inverse image on the small pro-étale site agrees with affine
inverse image after restriction to affine ind-étale objects. -/
def smallAbelianInverseImage_restrictionIso (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (affineIndEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology X) (topology X) ⋙ abelianInverseImage i ≅
      (smallProetalePullback i).sheafPullback AddCommGrpCat.{u + 1}
        (topology X) (topology Z) ⋙
        (affineIndEtaleInclusion Z).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (affineIndEtaleTopology Z) (topology Z) := by
  exact
    Functor.isoWhiskerLeft
        ((affineIndEtaleInclusion X).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (affineIndEtaleTopology X) (topology X))
        (abelianInverseImage_eq_ofContinuous i).symm ≪≫
      asIso (smallInverseImage_restrictionIso_mate i AddCommGrpCat.{u + 1})

end AffineIndEtale

end AlgebraicGeometry.Scheme.ProEt
