/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BigTopos
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Comparison of spaces-étale and big étale morphisms

Étale base change commutes with the inclusion into the big étale slice.
The induced geometric morphisms satisfy canonical factorization isomorphisms.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- The inverse image of relocalization factors through big étale inverse image
and identity-base relocalization. -/
def morphismCompBigIso (f : Y ⟶ X) :
    (morphismOfTopoi.{u, u + 1} f).inverseImage ≅
      (MorphismOfTopoiIn.comp (Big.morphismOfTopoi f)
        (morphismOfTopoi.{u, u + 1} (𝟙 Y))).inverseImage :=
  (Functor.sheafPushforwardContinuousComp'
    (Functor.isoWhiskerRight (relocalizationFunctor_id_iso Y) (Over.map f))
    (Type (u + 1)) (spacesEtaleTopology Y) (overEtaleTopology Y)
    (overEtaleTopology X)).symm

/-- Direct image along the spaces-étale morphism of topoi evaluates a sheaf on
the base-changed spaces-étale object. -/
theorem spacesEtaleMorphismOfTopoi_pushforward_obj_obj (f : Y ⟶ X)
    (F : Sheaf (spacesEtaleTopology Y) (Type (u + 1))) (U : spacesEtaleSite X) :
    ((spacesEtaleMorphismOfTopoi f).pushforward.obj F).1.obj (op U) =
      F.1.obj (op ((spacesEtalePullback f).obj U)) := sorry

/-- Inclusion of spaces-étale objects into the big slice commutes with base change. -/
def pullbackForgetIso (f : Y ⟶ X) :
    MorphismProperty.Over.forget (@Etale S) ⊤ X ⋙ Over.pullback f ≅
      spacesEtalePullback f ⋙ MorphismProperty.Over.forget (@Etale S) ⊤ Y :=
  (MorphismProperty.Over.pullbackCompForgetIso (P := @Etale S) (Q := ⊤) f).symm

/-- Restriction from big étale sheaves to spaces-étale sheaves commutes with direct image. -/
def pushforwardRestrictIso (f : Y ⟶ X) :
    (Big.morphismOfTopoi f).pushforward ⋙ (siteMorphismOfTopoi.{u, u + 1} X).pushforward ≅
      (siteMorphismOfTopoi.{u, u + 1} Y).pushforward ⋙ (spacesEtaleMorphismOfTopoi f).pushforward :=
  Functor.isoWhiskerRight (Big.directImageIsoPullbackPresentation f)
      (siteMorphismOfTopoi.{u, u + 1} X).pushforward ≪≫
    Functor.sheafPushforwardContinuousComp (relocalizationFunctor (𝟙 X))
      (Over.pullback f) (Type (u + 1)) (spacesEtaleTopology X)
      (overEtaleTopology X) (overEtaleTopology Y) ≪≫
    @Functor.sheafPushforwardContinuousIso _ _ _ _ _ _
      (Functor.isoWhiskerRight (relocalizationFunctor_id_iso X) (Over.pullback f) ≪≫
        pullbackForgetIso f ≪≫
        Functor.isoWhiskerLeft (spacesEtalePullback f) (relocalizationFunctor_id_iso Y).symm)
      (Type (u + 1)) _ (spacesEtaleTopology X) (overEtaleTopology Y)
      (Functor.isContinuous_comp (relocalizationFunctor (𝟙 X)) (Over.pullback f)
        (spacesEtaleTopology X) (overEtaleTopology X) (overEtaleTopology Y))
      (Functor.isContinuous_comp (spacesEtalePullback f) (relocalizationFunctor (𝟙 Y))
        (spacesEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology Y)) ≪≫
    (Functor.sheafPushforwardContinuousComp (spacesEtalePullback f)
      (relocalizationFunctor (𝟙 Y)) (Type (u + 1))
      (spacesEtaleTopology X) (spacesEtaleTopology Y) (overEtaleTopology Y)).symm

/-- The spaces-étale and big étale geometric-morphism square commutes on inverse images. -/
def spacesEtaleMorphismOfTopoiCompSiteIso (f : Y ⟶ X) :
    (MorphismOfTopoiIn.comp (spacesEtaleMorphismOfTopoi f)
        (siteMorphismOfTopoi.{u, u + 1} Y)).inverseImage ≅
      (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
        (Big.morphismOfTopoi f)).inverseImage :=
  Adjunction.leftAdjointUniq
    ((MorphismOfTopoiIn.comp (spacesEtaleMorphismOfTopoi f)
      (siteMorphismOfTopoi.{u, u + 1} Y)).adjunction.ofNatIsoRight (pushforwardRestrictIso f).symm)
    (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X) (Big.morphismOfTopoi f)).adjunction

/-- Spaces-étale inverse image factors through big étale inverse image and
identity-base relocalization. -/
def spacesEtaleMorphismOfTopoiCompBigIso (f : Y ⟶ X) :
    (spacesEtaleMorphismOfTopoi f).inverseImage ≅
      (MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
          (Big.morphismOfTopoi f))
        (morphismOfTopoi.{u, u + 1} (𝟙 Y))).inverseImage :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (spacesEtaleMorphismOfTopoi f).inverseImage
      (siteMorphismOfTopoi_comp_morphismOfTopoi_id.{u, u + 1} Y).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (spacesEtaleMorphismOfTopoiCompSiteIso f)
      (morphismOfTopoi.{u, u + 1} (𝟙 Y)).inverseImage

/-- Spaces-étale inverse image factors through the big-site inclusion and relocalization. -/
def spacesEtaleMorphismOfTopoiCompIso (f : Y ⟶ X) :
    (spacesEtaleMorphismOfTopoi f).inverseImage ≅
      (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
        (morphismOfTopoi.{u, u + 1} f)).inverseImage :=
  spacesEtaleMorphismOfTopoiCompBigIso f ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (siteMorphismOfTopoi.{u, u + 1} X).inverseImage
      (morphismCompBigIso f).symm

end AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig
