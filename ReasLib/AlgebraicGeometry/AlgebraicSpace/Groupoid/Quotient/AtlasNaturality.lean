/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Cartesian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.AtlasSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.IsoComma
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Associator
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Postcomposition

/-!
# Naturality of quotient-stack atlases

A morphism of groupoids induces the naturality square of their quotient atlases. If its source
square is cartesian, this naturality square is a two-fibre product.
-/

@[expose] public section

-- Exposed isomorphism data use private coherence specializations rather than public wrappers.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.Functor
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.Hom

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}

private def atlasIsoLeftAssoc (f : Hom G H) :
    (fppfAtlasULift G).comp (quotientStackMap f) ≅
      (stackInSetsULift.down G.U.left).comp
        ((fppfAtlas G).comp (quotientStackMap f)) :=
  CartesianBasedFunctor.associator (stackInSetsULift.down G.U.left)
    (fppfAtlas G) (quotientStackMap f)

private def atlasIsoInnerAssoc (f : Hom G H) :
    (fppfAtlas G).comp (quotientStackMap f) ≅
      (atlasToPreQuotient G).comp
        ((fppfQuotientStackPresentation G).comparison.comp (quotientStackMap f)) :=
  CartesianBasedFunctor.associator (atlasToPreQuotient G)
    (fppfQuotientStackPresentation G).comparison (quotientStackMap f)

private def atlasIsoPreAssoc (f : Hom G H) :
    (atlasToPreQuotient G).comp (prestackToQuotient f) ≅
      ((atlasToPreQuotient G).comp (prestackMap f)).comp
        (fppfQuotientStackPresentation H).comparison :=
  (CartesianBasedFunctor.associator (atlasToPreQuotient G) (prestackMap f)
    (fppfQuotientStackPresentation H).comparison).symm

/-- The prestack atlas followed by the induced prestack map is the object-space map followed
by the target prestack atlas. -/
theorem atlasToPreQuotient_comp_prestackMap (f : Hom G H) :
    (atlasToPreQuotient G).comp (prestackMap f) =
      (stackInSets.map f.obj.left).comp (atlasToPreQuotient H) := sorry

private def atlasPreIso (f : Hom G H) :
    (atlasToPreQuotient G).comp (prestackMap f) ≅
      (stackInSets.map f.obj.left).comp (atlasToPreQuotient H) :=
  eqToIso (atlasToPreQuotient_comp_prestackMap f)

private def atlasIsoRightAssoc (f : Hom G H) :
    ((stackInSets.map f.obj.left).comp (atlasToPreQuotient H)).comp
        (fppfQuotientStackPresentation H).comparison ≅
      (stackInSets.map f.obj.left).comp (fppfAtlas H) :=
  CartesianBasedFunctor.associator (stackInSets.map f.obj.left) (atlasToPreQuotient H)
    (fppfQuotientStackPresentation H).comparison

/-- The unlifted quotient atlases commute with the quotient-stack map up to the canonical
stackification comparison. -/
def atlasIsoCore (f : Hom G H) :
    (fppfAtlas G).comp (quotientStackMap f) ≅
      (stackInSets.map f.obj.left).comp (fppfAtlas H) :=
  atlasIsoInnerAssoc f ≪≫
    (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
        (atlasToPreQuotient G)).mapIso (quotientStackMap_comp f) ≪≫
    atlasIsoPreAssoc f ≪≫
    (CartesianBasedFunctor.postcomp (stackInSets G.U.left).p
        (fppfQuotientStackPresentation H).comparison).mapIso (atlasPreIso f) ≪≫
    atlasIsoRightAssoc f

private def atlasIsoULiftRightAssoc (f : Hom G H) :
    (stackInSetsULift.down G.U.left).comp
        (((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
          (fppfAtlasULift H)) ≅
      ((stackInSetsULift.down G.U.left).comp
          ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left))).comp
        (fppfAtlasULift H) :=
  (CartesianBasedFunctor.associator (stackInSetsULift.down G.U.left)
    ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left))
    (fppfAtlasULift H)).symm

private def atlasAlignedNatIso (f : Hom G H) :
    (stackInSets.map f.obj.left).toFunctor ⋙ (fppfAtlas H).toFunctor ≅
      ((stackInSets.map f.obj.left).toFunctor ⋙ (stackInSetsULift.up H.U.left).toFunctor) ⋙
        ((stackInSetsULift.down H.U.left).toFunctor ⋙ (fppfAtlas H).toFunctor) :=
  let L := (stackInSets.map f.obj.left).toFunctor
  let A := (fppfAtlas H).toFunctor
  let U := (stackInSetsULift.up H.U.left).toFunctor
  let D := (stackInSetsULift.down H.U.left).toFunctor
  let e₁ : L ⋙ A ≅ (L ⋙ 𝟭 _) ⋙ A :=
    isoWhiskerRight (Functor.rightUnitor L).symm A
  let e₂ : (L ⋙ 𝟭 _) ⋙ A ≅ (L ⋙ (U ⋙ D)) ⋙ A :=
    isoWhiskerRight (isoWhiskerLeft L (G := 𝟭 _) (H := U ⋙ D)
      (Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
        (stackInSets H.U.left).total).unitIso) A
  let e₃ : (L ⋙ (U ⋙ D)) ⋙ A ≅ ((L ⋙ U) ⋙ D) ⋙ A :=
    isoWhiskerRight (Functor.associator L U D).symm A
  let e₄ : ((L ⋙ U) ⋙ D) ⋙ A ≅ (L ⋙ U) ⋙ (D ⋙ A) :=
    Functor.associator (L ⋙ U) D A
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

private theorem atlasAlignedNatIso_hom_app (f : Hom G H)
    (x : (stackInSets G.U.left).total) :
    (atlasAlignedNatIso f).hom.app x =
      (fppfAtlas H).toFunctor.map
        ((Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1}
            (stackInSets H.U.left).total).unitIso.hom.app
          ((stackInSets.map f.obj.left).toFunctor.obj x)) := by
  simp only [atlasAlignedNatIso, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.rightUnitor_inv_app]
  erw [(fppfAtlas H).toFunctor.map_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp]
  rfl

private theorem atlasAlignedAssoc_vertical (f : Hom G H)
    (x : (stackInSets G.U.left).total) :
    IsHomLift (fppfQuotientStack H).p (𝟙 ((stackInSets G.U.left).p.obj x))
      ((atlasAlignedNatIso f).hom.app x) := sorry

private def atlasAlignedAssoc (f : Hom G H) :
    (stackInSets.map f.obj.left).comp (fppfAtlas H) ≅
      ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
        (fppfAtlasULift H) :=
  ObjectProperty.isoMk _ (BasedNatIso.mkNatIso
    (F := ((stackInSets.map f.obj.left).comp (fppfAtlas H)).toBasedFunctor)
    (G := (((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left)).comp
      (fppfAtlasULift H)).toBasedFunctor)
    (atlasAlignedNatIso f) (atlasAlignedAssoc_vertical f))

/-- The universe-aligned quotient atlases commute with the induced quotient-stack map up to
the canonical natural isomorphism. -/
def atlasIsoULift (f : Hom G H) :
    (fppfAtlasULift G).comp (quotientStackMap f) ≅
      ((stackInSetsULift.down G.U.left).comp
          ((stackInSets.map f.obj.left).comp (stackInSetsULift.up H.U.left))).comp
        (fppfAtlasULift H) :=
  atlasIsoLeftAssoc f ≪≫
    (CartesianBasedFunctor.precomp (fppfQuotientStack H).p
        (stackInSetsULift.down G.U.left)).mapIso (atlasIsoCore f ≪≫ atlasAlignedAssoc f) ≪≫
    atlasIsoULiftRightAssoc f

/-- The canonical invertible comparison cell between the atlas and object-map composites. -/
def atlasConeIso (f : Hom G H) :
    atlasULiftHom G ≫ isoCommaConeRight f ≅
      stackInSetsULift.map f.obj.left ≫ isoCommaConeBottom f :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (atlasIsoULift f)))

/-- The naturality square of the quotient atlases, with the stack of points of the source
object space as its apex. -/
def atlasCone (f : Hom G H) :
    PseudoPullbackCone (isoCommaConeRight f) (isoCommaConeBottom f) where
  pt := stackInSetsULift G.U.left
  fst := atlasULiftHom G
  snd := stackInSetsULift.map f.obj.left
  iso := atlasConeIso f

/-- The apex of the atlas naturality cone is the stack of points of the source object space. -/
theorem atlasCone_pt (f : Hom G H) :
    (atlasCone f).pt = stackInSetsULift G.U.left := rfl

/-- The first projection of the atlas naturality cone is the source quotient atlas. -/
theorem atlasCone_fst (f : Hom G H) :
    (atlasCone f).fst = atlasULiftHom G := rfl

/-- The second projection of the atlas naturality cone is induced by the object map. -/
theorem atlasCone_snd (f : Hom G H) :
    (atlasCone f).snd = stackInSetsULift.map f.obj.left := rfl

/-- The comparison cell of the atlas naturality cone is its canonical atlas isomorphism. -/
theorem atlasCone_iso (f : Hom G H) :
    (atlasCone f).iso = atlasConeIso f := rfl

/-- A cartesian source square of a groupoid morphism makes the atlas naturality square a
two-fibre product. -/
theorem atlasCone_isBilimit (f : Hom G H)
    (h_source : IsPullback f.arrow G.s H.s f.obj) :
    (atlasCone f).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.Hom
