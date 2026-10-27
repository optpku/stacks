/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso

/-!
# Étale topos functors of categories fibred in groupoids

A morphism of categories fibred in groupoids induces étale inverse- and
direct-image functors. Isomorphisms and composition of morphisms give explicit
transport isomorphisms of inverse-image functors.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism of étale topoi induced by a 1-morphism of categories fibred in
groupoids over `(Sch/S)_fppf`. -/
abbrev etaleMorphismOfTopoi {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn Z.etaleTopology Y.etaleTopology :=
  (toCartesianBasedFunctor h).morphismOfTopoiIn (StandardTopology.etale.overTopology S)

/-- Inverse image of étale sheaves along a 1-morphism of categories fibred in
groupoids, i.e. `h⁻¹`. -/
abbrev etaleInverseImage {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf Z.etaleTopology (Type (u + 1)) ⥤ Sheaf Y.etaleTopology (Type (u + 1)) :=
  (etaleMorphismOfTopoi h).inverseImage

/-- Direct image of étale sheaves along a 1-morphism of categories fibred in
groupoids, i.e. `h_*`. -/
abbrev etaleDirectImage {Y Z : GroupoidsOver S} (h : Y ⟶ Z)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P] :
    Sheaf Y.etaleTopology (Type (u + 1)) ⥤ Sheaf Z.etaleTopology (Type (u + 1)) :=
  (etaleMorphismOfTopoi h).pushforward

/-- Composite total functors are continuous for associated étale topologies. -/
instance toFunctor_comp_etale_isContinuous {Y Z W : GroupoidsOver S}
    (h : Y ⟶ Z) (k : Z ⟶ W) :
    (toFunctor h ⋙ toFunctor k).IsContinuous Y.etaleTopology W.etaleTopology :=
  Functor.isContinuous_comp (toFunctor h) (toFunctor k)
    Y.etaleTopology Z.etaleTopology W.etaleTopology

/-- Continuous sheaf pushforward along the cartesian total functor compared with
pushforward along `toFunctor`. -/
def etaleContinuousPushforwardIso {Y Z : GroupoidsOver S} (h : Y ⟶ Z) :
    (toCartesianBasedFunctor h).toFunctor.sheafPushforwardContinuous (Type (u + 1))
        Y.etaleTopology Z.etaleTopology ≅
      (toFunctor h).sheafPushforwardContinuous (Type (u + 1))
        Y.etaleTopology Z.etaleTopology :=
  sheafPushforwardContinuousIso (eqToIso (cartesian_toFunctor_eq h))
    (Type (u + 1)) Y.etaleTopology Z.etaleTopology

/-- An isomorphism `t : h ≅ k` of 1-morphisms induces `h⁻¹ ≅ k⁻¹` of étale
inverse images. -/
def etaleInverseImageIso {Y Z : GroupoidsOver S} {h k : Y ⟶ Z} (t : h ≅ k)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [HasWeakSheafify Z.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleInverseImage h ≅ etaleInverseImage k :=
  (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
      (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)) ≪≫
    etaleContinuousPushforwardIso h ≪≫
      sheafPushforwardContinuousIso (toFunctorIso t) (Type (u + 1))
        Y.etaleTopology Z.etaleTopology ≪≫
        (etaleContinuousPushforwardIso k).symm ≪≫
          (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
            (toCartesianBasedFunctor k) (StandardTopology.etale.overTopology S)).symm

/-- Inverse image of a composite 1-morphism compares with the composite of
inverse images. -/
def etaleInverseImage_compIso {Y Z W : GroupoidsOver S} (h : Y ⟶ Z) (k : Z ⟶ W)
    [HasSheafify Y.etaleTopology (Type (u + 1))]
    [HasSheafify Z.etaleTopology (Type (u + 1))]
    [HasWeakSheafify Z.etaleTopology (Type (u + 1))]
    [HasWeakSheafify W.etaleTopology (Type (u + 1))]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor h).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : Z.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor k).toFunctor.op.HasPointwiseRightKanExtension P]
    [∀ P : Y.totalᵒᵖ ⥤ Type (u + 1),
      (toCartesianBasedFunctor (h ≫ k)).toFunctor.op.HasPointwiseRightKanExtension P] :
    etaleInverseImage (h ≫ k) ≅ etaleInverseImage k ⋙ etaleInverseImage h :=
  (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
      (toCartesianBasedFunctor (h ≫ k)) (StandardTopology.etale.overTopology S)) ≪≫
    etaleContinuousPushforwardIso (h ≫ k) ≪≫
      sheafPushforwardContinuousIso
          (ObjectProperty.FullSubbicategory.toFunctor.compIso h k).symm (Type (u + 1))
          Y.etaleTopology W.etaleTopology ≪≫
        (sheafPushforwardContinuousComp (toFunctor h) (toFunctor k) (Type (u + 1))
            Y.etaleTopology Z.etaleTopology W.etaleTopology).symm ≪≫
          isoWhiskerRight (etaleContinuousPushforwardIso k).symm
              ((toFunctor h).sheafPushforwardContinuous (Type (u + 1))
                Y.etaleTopology Z.etaleTopology) ≪≫
            isoWhiskerRight
                (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
                  (toCartesianBasedFunctor k) (StandardTopology.etale.overTopology S)).symm
                ((toFunctor h).sheafPushforwardContinuous (Type (u + 1))
                  Y.etaleTopology Z.etaleTopology) ≪≫
              isoWhiskerLeft (etaleInverseImage k) (etaleContinuousPushforwardIso h).symm ≪≫
                isoWhiskerLeft (etaleInverseImage k)
                  (CartesianBasedFunctor.morphismOfTopoiIn.inverseImageComparisonIso
                    (toCartesianBasedFunctor h) (StandardTopology.etale.overTopology S)).symm

end AlgebraicGeometry.GroupoidsOver
