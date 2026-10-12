/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
public import stacks_project.Chap61.Lemma_61_12_21_Comparison
public import stacks_project.Chap61.Lemma_61_25_1_Comparison

/-!
# Affine closed immersions as morphisms of affine ind-étale topoi

A closed immersion of affine schemes induces the morphism of topoi associated
to the fully faithful cocontinuous lift `v : AffineIndEtale Z ⥤ AffineIndEtale X`.
Inverse image is sheafification of precomposition with `v`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]

/-- Affine ind-étale base change is left exact on type-valued sheaves, as the
sheaf pullback of a continuous right adjoint. -/
instance AffineIndEtale.baseChange_sheafPullback_preservesFiniteLimits
    (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((AffineIndEtale.baseChange i).sheafPullback (Type (u + 1))
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z)) := sorry

/-- The morphism of affine ind-étale topoi associated to the fully faithful
cocontinuous lift `v` of a closed immersion of affine schemes. -/
def AffineIndEtale.morphismOfTopoi (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    MorphismOfTopoiIn (affineIndEtaleTopology X) (affineIndEtaleTopology Z) :=
  (AffineIndEtale.lift i).morphismOfTopoiInOfCocontinuous
    (affineIndEtaleTopology Z) (affineIndEtaleTopology X)

/-- The morphism associated to `v` is the cocontinuous morphism of topoi of
affine ind-étale lift. -/
theorem AffineIndEtale.morphismOfTopoi_def (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    morphismOfTopoi i =
      (AffineIndEtale.lift i).morphismOfTopoiInOfCocontinuous
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  sorry

/-- Inverse image of the morphism associated to `v` is cocontinuous sheaf
pullback along affine ind-étale lift. -/
theorem AffineIndEtale.morphismOfTopoi_inverseImage (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    (morphismOfTopoi i).inverseImage =
      (AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  sorry

/-- Direct image of the morphism associated to `v` is cocontinuous sheaf
pushforward along affine ind-étale lift. -/
theorem AffineIndEtale.morphismOfTopoi_pushforward (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    (morphismOfTopoi i).pushforward =
      (AffineIndEtale.lift i).sheafPushforwardCocontinuous (Type (u + 1))
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  sorry

/-- Inverse image along the continuous functor `u` agrees with inverse image
of the morphism of topoi associated to `v`. -/
def AffineIndEtale.morphismOfTopoi_eq_ofContinuous (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    (AffineIndEtale.baseChange i).sheafPullback (Type (u + 1))
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      (morphismOfTopoi i).inverseImage :=
  Functor.CocontinuousLeftAdjoint.pullbackIsoInverseImage
    (AffineIndEtale.baseChange i) (AffineIndEtale.lift i)
    (AffineIndEtale.liftAdjunction i)

/-- The comparison of inverse images is the cocontinuous-left-adjoint
identification of sheaf pullback along `u` with inverse image along `v`. -/
theorem AffineIndEtale.morphismOfTopoi_eq_ofContinuous_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [HasWeakSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F] :
    morphismOfTopoi_eq_ofContinuous i =
      Functor.CocontinuousLeftAdjoint.pullbackIsoInverseImage
        (AffineIndEtale.baseChange i) (AffineIndEtale.lift i)
        (AffineIndEtale.liftAdjunction i) :=
  sorry

/-- Continuous direct image along `u` agrees with cocontinuous direct image
along `v`. -/
def AffineIndEtale.morphismOfTopoi_pushforwardIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    (A : Type (u + 2)) [Category.{u + 1} A]
    [∀ P : (AffineIndEtale Z)ᵒᵖ ⥤ A,
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension P] :
    (AffineIndEtale.baseChange i).sheafPushforwardContinuous A
        (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ≅
      (AffineIndEtale.lift i).sheafPushforwardCocontinuous A
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (AffineIndEtale.lift i) (AffineIndEtale.baseChange i) A
    (AffineIndEtale.liftAdjunction i)

/-- Inverse image of a type-valued sheaf along `v` is the sheaf associated to
the presheaf `V ↦ F(v(V))`. -/
theorem AffineIndEtale.inverseImage_sheafify (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1))) :
    ((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
          (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj F =
      (presheafToSheaf (affineIndEtaleTopology Z) (Type (u + 1))).obj
        ((AffineIndEtale.lift i).op ⋙ F.obj) :=
  sorry

/-- The canonical comparison from `F(v(V))` to the sections of the sheafified
presheaf `V ↦ F(v(V))`. -/
def AffineIndEtale.inverseImage_obj_to (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (V : AffineIndEtale Z) :
    F.obj.obj (op ((AffineIndEtale.lift i).obj V)) ⟶
      (((AffineIndEtale.lift i).sheafPullbackCocontinuous (Type (u + 1))
            (affineIndEtaleTopology Z) (affineIndEtaleTopology X)).obj F).obj.obj
        (op V) :=
  ((sheafificationAdjunction (affineIndEtaleTopology Z) (Type (u + 1))).unit.app
      ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V)

/-- The comparison `inverseImage_obj_to` is the sheafification unit at `v(V)`. -/
theorem AffineIndEtale.inverseImage_obj_to_app (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (V : AffineIndEtale Z) :
    inverseImage_obj_to i F V =
      ((sheafificationAdjunction (affineIndEtaleTopology Z) (Type (u + 1))).unit.app
          ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V) :=
  sorry

/-- On a weakly contractible affine ind-étale object, the sheafification unit
identifies `i⁻¹ F(V)` with `F(v(V))`. -/
instance AffineIndEtale.inverseImage_obj_to_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    (F : Sheaf (affineIndEtaleTopology X) (Type (u + 1)))
    (V : AffineIndEtale Z)
    [(affineIndEtaleTopology Z).IsWeaklyContractible V] :
    IsIso (inverseImage_obj_to i F V) :=
  sorry

/-- Abelian inverse image on affine ind-étale sites along `v`, as sheafification
of precomposition. -/
def AffineIndEtale.abelianInverseImage (i : Z ⟶ X) [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}] :
    Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1} :=
  (AffineIndEtale.lift i).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
    (affineIndEtaleTopology Z) (affineIndEtaleTopology X)

/-- Abelian inverse image is cocontinuous sheaf pullback along affine ind-étale
lift. -/
theorem AffineIndEtale.abelianInverseImage_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}] :
    abelianInverseImage i =
      (AffineIndEtale.lift i).sheafPullbackCocontinuous AddCommGrpCat.{u + 1}
        (affineIndEtaleTopology Z) (affineIndEtaleTopology X) :=
  sorry

/-- Abelian inverse image of a sheaf along `v` is the sheaf associated to the
presheaf `V ↦ F(v(V))`. -/
theorem AffineIndEtale.abelianInverseImage_sheafify (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (abelianInverseImage i).obj F =
      (presheafToSheaf (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}).obj
        ((AffineIndEtale.lift i).op ⋙ F.obj) :=
  sorry

/-- The canonical comparison from `F(v(V))` to the sections of abelian inverse
image along `v`. -/
def AffineIndEtale.abelianInverseImage_obj_to (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (V : AffineIndEtale Z) :
    F.obj.obj (op ((AffineIndEtale.lift i).obj V)) ⟶
      ((abelianInverseImage i).obj F).obj.obj (op V) :=
  ((sheafificationAdjunction (affineIndEtaleTopology Z)
      AddCommGrpCat.{u + 1}).unit.app
    ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V)

/-- The abelian comparison `abelianInverseImage_obj_to` is the sheafification
unit at `v(V)`. -/
theorem AffineIndEtale.abelianInverseImage_obj_to_app (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasWeakSheafify (affineIndEtaleTopology Z) AddCommGrpCat.{u + 1}]
    (F : Sheaf (affineIndEtaleTopology X) AddCommGrpCat.{u + 1})
    (V : AffineIndEtale Z) :
    abelianInverseImage_obj_to i F V =
      ((sheafificationAdjunction (affineIndEtaleTopology Z)
          AddCommGrpCat.{u + 1}).unit.app
        ((AffineIndEtale.lift i).op ⋙ F.obj)).app (op V) :=
  sorry

/-- Affine ind-étale inclusion followed by small pro-étale pullback is
continuous. -/
instance AffineIndEtale.inclusion_comp_smallProetalePullback_isContinuous
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (affineIndEtaleInclusion X ⋙ smallProetalePullback i).IsContinuous
      (affineIndEtaleTopology X) (topology Z) :=
  Functor.isContinuous_comp (affineIndEtaleInclusion X) (smallProetalePullback i)
    (affineIndEtaleTopology X) (topology X) (topology Z)

/-- Affine ind-étale base change followed by inclusion is continuous. -/
instance AffineIndEtale.baseChange_comp_inclusion_isContinuous
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (AffineIndEtale.baseChange i ⋙ affineIndEtaleInclusion Z).IsContinuous
      (affineIndEtaleTopology X) (topology Z) :=
  Functor.isContinuous_comp (AffineIndEtale.baseChange i) (affineIndEtaleInclusion Z)
    (affineIndEtaleTopology X) (affineIndEtaleTopology Z) (topology Z)

/-- Direct-image comparison of the affine/small base-change square. -/
def AffineIndEtale.smallInverseImage_restrictionIso_pushforward (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (smallProetalePullback i).sheafPushforwardContinuous (Type (u + 1))
        (topology X) (topology Z) ⋙
      affineIndEtaleRestriction X ≅
      affineIndEtaleRestriction Z ⋙
        (AffineIndEtale.baseChange i).sheafPushforwardContinuous (Type (u + 1))
          (affineIndEtaleTopology X) (affineIndEtaleTopology Z) :=
  (affineIndEtaleInclusion X).sheafPushforwardContinuousComp'
      (Iso.refl (affineIndEtaleInclusion X ⋙ smallProetalePullback i))
      (Type (u + 1)) (affineIndEtaleTopology X) (topology X) (topology Z) ≪≫
    (Functor.sheafPushforwardContinuousIso (baseChange_comp_inclusion i).symm
      (Type (u + 1)) (affineIndEtaleTopology X) (topology Z)) ≪≫
    ((AffineIndEtale.baseChange i).sheafPushforwardContinuousComp'
      (Iso.refl (AffineIndEtale.baseChange i ⋙ affineIndEtaleInclusion Z))
      (Type (u + 1)) (affineIndEtaleTopology X) (affineIndEtaleTopology Z)
      (topology Z)).symm

/-- Mate of the affine/small pushforward comparison along the continuous
sheaf adjunctions of `u` and of small pro-étale pullback. -/
def AffineIndEtale.smallInverseImage_restrictionIso_mate (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback i).op.HasLeftKanExtension P] :
    affineIndEtaleRestriction X ⋙
        (AffineIndEtale.baseChange i).sheafPullback (Type (u + 1))
          (affineIndEtaleTopology X) (affineIndEtaleTopology Z) ⟶
      (smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z :=
  (mateEquiv
      ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
        (topology X) (topology Z))
      ((AffineIndEtale.baseChange i).sheafAdjunctionContinuous
        (Type (u + 1)) (affineIndEtaleTopology X)
        (affineIndEtaleTopology Z))).symm
    (TwoSquare.mk _ _ _ _
      (smallInverseImage_restrictionIso_pushforward i).hom)

/-- The affine/small inverse-image mate is the mate of the pushforward
comparison 2-cell. -/
theorem AffineIndEtale.smallInverseImage_restrictionIso_mate_def (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback i).op.HasLeftKanExtension P] :
    smallInverseImage_restrictionIso_mate i =
      (mateEquiv
          ((smallProetalePullback i).sheafAdjunctionContinuous (Type (u + 1))
            (topology X) (topology Z))
          ((AffineIndEtale.baseChange i).sheafAdjunctionContinuous
            (Type (u + 1)) (affineIndEtaleTopology X)
            (affineIndEtaleTopology Z))).symm
        (TwoSquare.mk _ _ _ _
          (smallInverseImage_restrictionIso_pushforward i).hom) :=
  sorry

/-- The affine/small inverse-image mate is an isomorphism. -/
instance AffineIndEtale.smallInverseImage_restrictionIso_mate_isIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback i).op.HasLeftKanExtension P] :
    IsIso (smallInverseImage_restrictionIso_mate i) :=
  sorry

/-- Inverse image along `i_proétale` on small pro-étale sites, after restriction
to affine ind-étale objects, agrees with inverse image along `v`. -/
def AffineIndEtale.smallInverseImage_restrictionIso (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F]
    [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback i).op.HasLeftKanExtension P] :
    affineIndEtaleRestriction X ⋙ (morphismOfTopoi i).inverseImage ≅
      (smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z :=
  Functor.isoWhiskerLeft (affineIndEtaleRestriction X)
      (morphismOfTopoi_eq_ofContinuous i).symm ≪≫
    asIso (smallInverseImage_restrictionIso_mate i)

/-- The small-site comparison is an isomorphism of inverse-image functors after
affine ind-étale restriction. -/
def AffineIndEtale.smallInverseImage_restrictionIso_app (i : Z ⟶ X)
    [IsClosedImmersion i]
    [HasSheafify (topology X) (Type (u + 1))]
    [HasSheafify (topology Z) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology X) (Type (u + 1))]
    [HasSheafify (affineIndEtaleTopology Z) (Type (u + 1))]
    [∀ P : (AffineIndEtale X)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.baseChange i).op.HasLeftKanExtension P]
    [∀ F : (AffineIndEtale Z)ᵒᵖ ⥤ Type (u + 1),
      (AffineIndEtale.lift i).op.HasPointwiseRightKanExtension F]
    [∀ P : X.ProEtᵒᵖ ⥤ Type (u + 1),
      (smallProetalePullback i).op.HasLeftKanExtension P]
    (F : Sheaf (topology X) (Type (u + 1))) :
    (affineIndEtaleRestriction X ⋙ (morphismOfTopoi i).inverseImage).obj F ≅
      ((smallProetalePullback i).sheafPullback (Type (u + 1))
          (topology X) (topology Z) ⋙
        affineIndEtaleRestriction Z).obj F :=
  (smallInverseImage_restrictionIso i).app F

end AlgebraicGeometry.Scheme.ProEt
