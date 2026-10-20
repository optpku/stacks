/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.CategoryTheory.Sites.Over.Pushforward
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SmallLocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.Relocalization
public import ReasLib.CategoryTheory.Equivalence.TransferSquare
public import ReasLib.CategoryTheory.Sites.Localization.Subcanonical

public section

noncomputable section
universe u


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open RingedSite.ToposHom
open CategoryTheory.GrothendieckTopology


namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The small-étale morphism of `g`, transported along the identifications
`(U_étale, 𝒪_U) ≅ localization of X at U` and
`(V_étale, 𝒪_V) ≅ localization of Y at V`. -/
@[expose]
def etaleRelocalizeConjugateScheme :
    RingedSite.ToposHom
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u}
      ((ringedSite X).localization (smallEtaleSite.mk p))
      (ringedSite (ofOver U))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
      (etaleLocalizationIso_inv_toToposHom p)
      (@RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u}
        (ringedSite (ofOver U)) (ringedSite (ofOver V))
        ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
        (ringedToposHom g) (etaleLocalizationIso_hom_toToposHom q))

/-- Relocalization along `smallEtaleInclusion_mkIso p`, identifying the spaces-étale
localization at the image of `U` with the localization at `spacesEtaleSite.mk p`. -/
@[expose]
def etaleRelocalizeMkRelocalization_source :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p)) :=
  spacesRingedHom.relocalization (smallEtaleInclusion_mkIso p).hom

/-- Relocalization along the inverse of `smallEtaleInclusion_mkIso q`. -/
@[expose]
def etaleRelocalizeMkRelocalization_target :
    RingedSite.ToposHom
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q))
      ((spacesRingedSite Y).localization
        ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) :=
  spacesRingedHom.relocalization (smallEtaleInclusion_mkIso q).inv

/-- The spaces-étale conjugate of `g`, transported from `spacesEtaleSite.mk` to the
small-étale inclusion images. -/
@[expose]
def etaleRelocalizeSpacesConjugate (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite Y).localization
        ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) :=
  @RingedSite.ToposHom.comp
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization
        ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) _ _ _
      (etaleRelocalizeMkRelocalization_source p)
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
          ((spacesRingedSite Y).localization (spacesEtaleSite.mk q))
          ((spacesRingedSite Y).localization
            ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) _ _ _
          (spacesEtaleRelocalizeConjugate p g f q hcomm)
          (etaleRelocalizeMkRelocalization_target q))

/-- The spaces-étale localization of `f` at `c`, transported from `spacesEtaleSite.mk` to the
small-étale inclusion images. -/
@[expose]
def etaleRelocalizeSpacesLocalization (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite Y).localization
        ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) :=
  @RingedSite.ToposHom.comp
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization
        ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) _ _ _
      (etaleRelocalizeMkRelocalization_source p)
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
          ((spacesRingedSite Y).localization (spacesEtaleSite.mk q))
          ((spacesRingedSite Y).localization
            ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q))) _ _ _
          (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
            (spacesEtalePullbackLift p g f q hcomm))
          (etaleRelocalizeMkRelocalization_target q))

/-- Direct-image comparison of the transported spaces-étale conjugate of `g` with the
transported spaces-étale localization of `f` at `c`. -/
@[expose]
def etaleRelocalizeSpacesBridge_homIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeSpacesConjugate p g f q hcomm).toTopos.pushforward ≅
      (etaleRelocalizeSpacesLocalization p g f q hcomm).toTopos.pushforward :=
  Functor.isoWhiskerLeft
      (etaleRelocalizeMkRelocalization_source p).toTopos.pushforward
      (Functor.isoWhiskerRight (spacesEtaleRelocalizeIso_homIso p g f q hcomm)
        (etaleRelocalizeMkRelocalization_target q).toTopos.pushforward)

/-- The small-étale morphism of `g`, transported to the localizations of `X` and `Y` by the
small-versus-spaces comparison and the étale localization identifications. -/
@[expose]
def etaleRelocalizeConjugate (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @RingedSite.ToposHom.comp
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
      (smallEtaleLocalizationComparison X (smallEtaleSite.mk p))
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization
            ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
          ((spacesRingedSite Y).localization
            ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q)))
          ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
          (etaleRelocalizeSpacesConjugate p g f q hcomm)
          (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)))

/-- The representable-parameter localization of `f_small` at the parameter corresponding to `g`, presented by
conjugating the spaces-étale localization  along the small-versus-spaces
comparisons. -/
@[expose]
def etaleRelocalizeLocalization (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @RingedSite.ToposHom.comp
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((spacesRingedSite X).localization
        ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
      (smallEtaleLocalizationComparison X (smallEtaleSite.mk p))
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization
            ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)))
          ((spacesRingedSite Y).localization
            ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q)))
          ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
          (etaleRelocalizeSpacesLocalization p g f q hcomm)
          (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)))

/-- Direct-image comparison of the middle comparison
`etaleRelocalizeConjugate` ≅ `etaleRelocalizeLocalization`. -/
@[expose]
def etaleRelocalizeViaSpacesIso_homIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugate p g f q hcomm).toTopos.pushforward ≅
      (etaleRelocalizeLocalization p g f q hcomm).toTopos.pushforward :=
  Functor.isoWhiskerLeft
      (smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.pushforward
      (Functor.isoWhiskerRight (etaleRelocalizeSpacesBridge_homIso p g f q hcomm)
        (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)).toTopos.pushforward)

/-- The direct-image comparison respects the structure-sheaf map. -/
private theorem etaleRelocalizeViaSpacesIso_comm (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugate p g f q hcomm).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans (etaleRelocalizeViaSpacesIso_homIso p g f q hcomm).hom).app
        ((ringedSite X).localization (smallEtaleSite.mk p)).structureSheaf =
      (etaleRelocalizeLocalization p g f q hcomm).directStructureMap := sorry

/-- The middle comparison identifying the spaces-route conjugate
`etaleRelocalizeConjugate` with the spaces-route localization
`etaleRelocalizeLocalization`. -/
@[expose]
def etaleRelocalizeViaSpacesIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugate p g f q hcomm)
      (etaleRelocalizeLocalization p g f q hcomm) where
  homIso := etaleRelocalizeViaSpacesIso_homIso p g f q hcomm
  comm := by exact etaleRelocalizeViaSpacesIso_comm p g f q hcomm

/-- On a sheaf on the small-étale source slice, the comparison is obtained by
applying the target comparison functor to the spaces-étale bridge at its source
comparison image. This specifies the actual component of the constructed 2-cell. -/
theorem etaleRelocalizeViaSpacesIso_homIso_app (hcomm : p ≫ f = g ≫ q)
    (F : Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (Type u)) :
    (etaleRelocalizeViaSpacesIso p g f q hcomm).homIso.hom.app F =
      (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)).toTopos.pushforward.map
        ((etaleRelocalizeSpacesBridge_homIso p g f q hcomm).hom.app
          ((smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.pushforward.obj F)) :=
  rfl


end AlgebraicGeometry.AlgebraicSpace


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}}


variable {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X) [Etale p]

/-- The image of a scheme slice object, rebased to the ordinary spaces-site object. -/
@[expose]
def sliceInclusion : Over (smallEtaleSite.mk p (hφ := inferInstance)) ⥤ Over (spacesEtaleSite.mk p) :=
  smallEtaleOverPost X (smallEtaleSite.mk p (hφ := inferInstance)) ⋙ Over.map (smallEtaleInclusion_mkIso p).hom

/-- The identity on the underlying space respects the localization chart maps. -/
private theorem localizationSquare_obj_w (W : smallEtaleSite (ofOver U)) :
    (𝟙 _) ≫ ((smallEtaleToSpaces (ofOver U) ⋙ spacesEtaleLocalizationFunctor p).obj W).left.hom = ((etaleLocalizationFunctor p ⋙ sliceInclusion p).obj W).left.hom := sorry

/-- The identity chart comparison respects the slice structure maps. -/
private theorem localizationSquare_slice_w (W : smallEtaleSite (ofOver U)) :
    (MorphismProperty.Over.isoMk (Iso.refl _) (by exact localizationSquare_obj_w p W) :
      ((etaleLocalizationFunctor p ⋙ sliceInclusion p).obj W).left ≅ ((smallEtaleToSpaces (ofOver U) ⋙ spacesEtaleLocalizationFunctor p).obj W).left).hom ≫ ((smallEtaleToSpaces (ofOver U) ⋙ spacesEtaleLocalizationFunctor p).obj W).hom =
      ((etaleLocalizationFunctor p ⋙ sliceInclusion p).obj W).hom := sorry

/-- The identity on the underlying space compares the two localization paths. -/
private def localizationSquareObjIso (W : smallEtaleSite (ofOver U)) :
    (etaleLocalizationFunctor p ⋙ sliceInclusion p).obj W ≅ (smallEtaleToSpaces (ofOver U) ⋙ spacesEtaleLocalizationFunctor p).obj W :=
  Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl _)
    (by exact localizationSquare_obj_w p W)) (by exact localizationSquare_slice_w p W)

/-- The identity comparisons commute with chart morphisms. -/
private theorem localizationSquare_naturality {A B : smallEtaleSite (ofOver U)}
    (k : A ⟶ B) :
    (etaleLocalizationFunctor p ⋙ sliceInclusion p).map k ≫ (localizationSquareObjIso p B).hom =
      (localizationSquareObjIso p A).hom ≫ (smallEtaleToSpaces (ofOver U) ⋙ spacesEtaleLocalizationFunctor p).map k := sorry

/-- Postcomposition to the slice commutes with passage from schemes to spaces. -/
def localizationSquare : (etaleLocalizationFunctor p ⋙ sliceInclusion p) ≅ (smallEtaleToSpaces (ofOver U) ⋙ spacesEtaleLocalizationFunctor p) :=
  NatIso.ofComponents (localizationSquareObjIso p)
    (by intro A B k; exact localizationSquare_naturality p k)

/-- The identity on the underlying space respects the recovered localization maps. -/
private theorem localizationInverseSquare_obj_w (W : Over (smallEtaleSite.mk p)) :
    (𝟙 _) ≫ ((sliceInclusion p ⋙ spacesEtaleLocalizationInverse p).obj W).hom = ((etaleLocalizationInverse p ⋙ smallEtaleToSpaces (ofOver U)).obj W).hom := sorry

/-- The identity on the underlying space compares the inverse localization paths. -/
private def localizationInverseSquareObjIso (W : Over (smallEtaleSite.mk p)) :
    (etaleLocalizationInverse p ⋙ smallEtaleToSpaces (ofOver U)).obj W ≅ (sliceInclusion p ⋙ spacesEtaleLocalizationInverse p).obj W :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by exact localizationInverseSquare_obj_w p W)

/-- Inverse localization comparisons commute with slice morphisms. -/
private theorem localizationInverseSquare_naturality {A B : Over (smallEtaleSite.mk p)}
    (k : A ⟶ B) :
    (etaleLocalizationInverse p ⋙ smallEtaleToSpaces (ofOver U)).map k ≫ (localizationInverseSquareObjIso p B).hom =
      (localizationInverseSquareObjIso p A).hom ≫ (sliceInclusion p ⋙ spacesEtaleLocalizationInverse p).map k := sorry

/-- Recovering a scheme slice arrow commutes with passage to spaces. -/
def localizationInverseSquare : (etaleLocalizationInverse p ⋙ smallEtaleToSpaces (ofOver U)) ≅ (sliceInclusion p ⋙ spacesEtaleLocalizationInverse p) :=
  NatIso.ofComponents (localizationInverseSquareObjIso p)
    (by intro A B k; exact localizationInverseSquare_naturality p k)

/-- Restriction along a slice isomorphism is an equivalence of sheaf categories. -/
instance overIsoRestriction_isEquivalence {Z : AlgebraicSpace S}
    {A B : spacesEtaleSite Z} (e : A ≅ B) :
    ((Over.map e.hom).sheafPushforwardContinuous (Type u)
      ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B)).IsEquivalence := sorry

/-- The composite slice inclusion is continuous. -/
instance sliceInclusion_isContinuous :
    (sliceInclusion p).IsContinuous ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) :=
  Functor.isContinuous_comp (smallEtaleOverPost X (smallEtaleSite.mk p (hφ := inferInstance)))
    (Over.map (smallEtaleInclusion_mkIso p).hom)
    ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
    ((spacesEtaleTopology X).over ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p (hφ := inferInstance))))
    ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))

/-- Continuity of the upper path of the localization square. -/
instance localizationSquare_left_isContinuous :
    (etaleLocalizationFunctor p ⋙ sliceInclusion p).IsContinuous
      (smallEtaleTopology (ofOver U)) ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) :=
  Functor.isContinuous_comp (etaleLocalizationFunctor p) (sliceInclusion p)
    (smallEtaleTopology (ofOver U)) ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
    ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))

/-- The source slice equivalence with inverse exactly the extension used in the slice comparison. -/
@[expose]
def sliceEquivalence :
    Sheaf ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) (Type u) ≌
      Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance))) (Type u) :=
  (((Over.map (smallEtaleInclusion_mkIso p).hom).sheafAdjunctionCocontinuous (Type u)
      ((spacesEtaleTopology X).over ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p (hφ := inferInstance))))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))).comp
    ((smallEtaleOverPost X (smallEtaleSite.mk p (hφ := inferInstance))).sheafAdjunctionCocontinuous (Type u)
      ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
      ((spacesEtaleTopology X).over ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p (hφ := inferInstance)))))).toEquivalence

/-- The restriction square induced by the identity-on-space localization square. -/
@[expose]
def restrictionSquare :
    (spacesEtaleLocalizationFunctor p).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology (ofOver U)) ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) ⋙
      (EtaleTopos.siteEquivalence (ofOver U)).functor ≅
    (sliceEquivalence p).functor ⋙
      (etaleLocalizationFunctor p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology (ofOver U)) ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance))) :=
  (Functor.sheafPushforwardContinuousComp'
    (localizationSquare p).symm (Type u) (smallEtaleTopology (ofOver U))
      (spacesEtaleTopology (ofOver U)) ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))) ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ (Type u)
      (smallEtaleTopology (ofOver U)) ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))).symm

/-- Source localization commutes with small-to-spaces extension by the canonical mate. -/
@[expose]
def sourceIso :
    (etaleLocalizationIso_inv_toToposHom p).toTopos.pushforward ⋙
        (EtaleTopos.siteEquivalence (ofOver U)).inverse ≅
      (sliceEquivalence p).inverse ⋙
        (spacesEtaleLocalizationIso_inv_toToposHom p).toTopos.pushforward :=
  (sliceEquivalence p).transferSquare (EtaleTopos.siteEquivalence (ofOver U)) _ _ (restrictionSquare p)


/-- A slice isomorphism identifies the slice topologies in either direction. -/
instance overIso_inverse_dense {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (e : A ≅ B) :
    (Over.mapIso e).inverse.IsDenseSubsite
      ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A) :=
  @Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _
    ((spacesEtaleTopology Z).over A) _ _ ((spacesEtaleTopology Z).over B) (Over.mapIso e)
    (inferInstanceAs ((Over.map e.hom).IsCocontinuous _ _))
    (inferInstanceAs ((Over.map e.inv).IsCocontinuous _ _))

/-- Restriction along an isomorphism is the specified right adjoint to restriction
along its inverse, hence identifies with the existing right-Kan extension. -/
@[expose]
def overIsoPushforward {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (e : A ≅ B) :
    (Over.map e.hom).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B) ≅
      (Over.map e.inv).sheafPushforwardCocontinuous (Type u)
        ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A) :=
  Adjunction.rightAdjointUniq
    ((Over.mapIso e).sheafCongr ((spacesEtaleTopology Z).over A)
      ((spacesEtaleTopology Z).over B) (Type u)).toAdjunction
    ((Over.map e.inv).sheafAdjunctionCocontinuous (Type u)
      ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A))

/-- Continuity of the spaces path in the inverse localization square. -/
instance inverseSquare_right_isContinuous :
    (sliceInclusion p ⋙ spacesEtaleLocalizationInverse p).IsContinuous
      ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance))) (spacesEtaleTopology (ofOver U)) :=
  Functor.isContinuous_comp (sliceInclusion p) (spacesEtaleLocalizationInverse p)
    ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
    ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) (spacesEtaleTopology (ofOver U))

/-- Target localization commutes with spaces-to-small restriction and the mk-object rebase. -/
@[expose]
def targetIso :
    (EtaleTopos.siteEquivalence (ofOver U)).functor ⋙
        (etaleLocalizationIso_hom_toToposHom p).toTopos.pushforward ≅
      (spacesEtaleLocalizationIso_hom_toToposHom p).toTopos.pushforward ⋙
        (etaleRelocalizeMkRelocalization_target p).toTopos.pushforward ⋙
          (smallEtaleLocalizationComparisonInv X (smallEtaleSite.mk p (hφ := inferInstance))).toTopos.pushforward :=
  Functor.sheafPushforwardContinuousComp' (localizationInverseSquare p) (Type u)
      ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance))) (smallEtaleTopology (ofOver U))
      (spacesEtaleTopology (ofOver U)) ≪≫
    (Functor.sheafPushforwardContinuousComp (sliceInclusion p) (spacesEtaleLocalizationInverse p)
      (Type u) ((smallEtaleTopology X).over (smallEtaleSite.mk p (hφ := inferInstance)))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) (spacesEtaleTopology (ofOver U))).symm ≪≫
    Functor.isoWhiskerLeft (spacesEtaleLocalizationIso_hom_toToposHom p).toTopos.pushforward
      (Functor.isoWhiskerRight (overIsoPushforward (smallEtaleInclusion_mkIso p))
        (smallEtaleLocalizationComparisonInv X (smallEtaleSite.mk p (hφ := inferInstance))).toTopos.pushforward)

/-- The direct-image comparison for an arbitrary morphism, before localization.
It is induced by the actual base-change square of site functors. -/
@[expose]
def morphismPushforwardIso {Z W : AlgebraicSpace S} (g : Z ⟶ W) :
    (ringedToposHom g).toTopos.pushforward ≅
      (EtaleTopos.siteEquivalence Z).inverse ⋙
        (spacesRingedToposHom g).toTopos.pushforward ⋙
          (EtaleTopos.siteEquivalence W).functor :=
  Functor.isoWhiskerLeft (EtaleTopos.siteEquivalence Z).inverse
    (Functor.sheafPushforwardContinuousComp'
      (smallEtaleInclusion_comp_spacesEtalePullback g) (Type u)
      (smallEtaleTopology W) (spacesEtaleTopology W) (spacesEtaleTopology Z)).symm

variable {V : Over S} {Y : AlgebraicSpace S}
variable (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y) [Etale q]

/-- The actual scheme conjugate is compared with the spaces-route conjugate
by the source mate, base-change square, and target restriction square. -/
@[expose]
def conjugateSchemeIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugateScheme p g q).toTopos.pushforward ≅
      (etaleRelocalizeConjugate p g f q hcomm).toTopos.pushforward :=
  Functor.isoWhiskerLeft (etaleLocalizationIso_inv_toToposHom p).toTopos.pushforward
      (Functor.isoWhiskerRight (morphismPushforwardIso g)
        (etaleLocalizationIso_hom_toToposHom q).toTopos.pushforward) ≪≫
    Functor.isoWhiskerRight (sourceIso p)
      ((spacesRingedToposHom g).toTopos.pushforward ⋙
        (EtaleTopos.siteEquivalence (ofOver V)).functor ⋙
          (etaleLocalizationIso_hom_toToposHom q).toTopos.pushforward) ≪≫
    Functor.isoWhiskerLeft (sliceEquivalence p).inverse
      (Functor.isoWhiskerLeft (spacesEtaleLocalizationIso_inv_toToposHom p).toTopos.pushforward
        (Functor.isoWhiskerLeft (spacesRingedToposHom g).toTopos.pushforward (targetIso q)))

/-- The direct-image comparison respects the structure-sheaf map. -/
private theorem conjugateSchemeTwoIso_comm (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugateScheme p g q).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans (conjugateSchemeIso p g f q hcomm).hom).app
        ((ringedSite X).localization (smallEtaleSite.mk p)).structureSheaf =
      (etaleRelocalizeConjugate p g f q hcomm).directStructureMap := sorry

/-- Ringed version of the explicit scheme/spaces comparison. Its compatibility
is the naturality of the structure-sheaf restriction and extension maps. -/
@[expose]
def conjugateSchemeTwoIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p (hφ := inferInstance)))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugateScheme p g q)
      (etaleRelocalizeConjugate p g f q hcomm) where
  homIso := conjugateSchemeIso p g f q hcomm
  comm := by exact conjugateSchemeTwoIso_comm p g f q hcomm

end AlgebraicGeometry.AlgebraicSpace.Relocalization


namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The actual representable-localization equivalence for the small étale site. -/
@[expose]
def etaleSliceEquivalence (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    Sheaf ((smallEtaleTopology X).over U) (Type u) ≌ Over (etaleRepresentable U) :=
  SubcanonicalSlice.equivalence (smallEtaleTopology X) U

end AlgebraicGeometry.AlgebraicSpace


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.GrothendieckTopology


namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}}

/-- Extension to spaces commutes with restriction to a representable slice.
This is the mate of the literal `Over.post`/forget square. -/
@[expose]
def extensionOverIso (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    (smallEtaleTopology X).overPullback (Type u) U ⋙
        (smallEtaleLocalizationSheafEquivalence X U).inverse ≅
      (EtaleTopos.siteEquivalence X).inverse ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((smallEtaleToSpaces X).obj U) :=
  (EtaleTopos.siteEquivalence X).transferSquare (smallEtaleLocalizationSheafEquivalence X U) _ _
    ((smallEtaleToSpaces X).sheafPushforwardOverPostComp U (Type u))

/-- The transported spaces inverse image is compared with the specified small inverse image
by uniqueness of the left adjoint to the existing direct-image comparison. -/
@[expose]
def morphismInverseImageIso {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (EtaleTopos.siteEquivalence Y).inverse ⋙ (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (EtaleTopos.siteEquivalence X).functor ≅ (morphismOfTopoi f).inverseImage :=
  Adjunction.leftAdjointUniq
    ((((EtaleTopos.siteEquivalence Y).symm.toAdjunction.comp
      (spacesRingedToposHom f).toTopos.adjunction).comp
        (EtaleTopos.siteEquivalence X).toAdjunction).ofNatIsoRight (morphismPushforwardIso f).symm)
    (morphismOfTopoi f).adjunction

/-- Relocalization has restriction as its inverse image, with its specified right adjoint. -/
@[expose]
def relocalizationInverseImageIso {X : AlgebraicSpace S} {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (spacesRingedHom.relocalization c).toTopos.inverseImage ≅
      (Over.map c).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) :=
  Adjunction.leftAdjointUniq (spacesRingedHom.relocalization c).toTopos.adjunction
    ((Over.map c).sheafAdjunctionCocontinuous (Type u)
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V))

/-- The actual mate for the ambient square of spaces-site localization; no inverse is chosen. -/
@[expose]
def spacesLocalizationComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : spacesEtaleSite Y) :
    (spacesEtaleTopology Y).overPullback (Type u) V ⋙
        (spacesRingedHom.localizationToposHom f V).toTopos.inverseImage ⟶
      (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((spacesEtalePullback f).obj V) :=
  ((mateEquiv (spacesRingedToposHom f).toTopos.adjunction
    (spacesRingedHom.localizationToposHom f V).toTopos.adjunction).symm
      ((spacesEtalePullback f).sheafPushforwardOverPostComp V (Type u)).inv).natTrans

/-- The ambient square for spaces localization at an actual site arrow.
It is formed from the previous mate and strict restriction along `Over.map c`. -/
@[expose]
def spacesAtComparison {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : spacesEtaleSite Y)
    {U : spacesEtaleSite X} (c : U ⟶ (spacesEtalePullback f).obj V) :
    (spacesEtaleTopology Y).overPullback (Type u) V ⋙
        (spacesRingedHom.localizationAt f V c).toTopos.inverseImage ⟶
      (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) U :=
  Functor.whiskerRight (spacesLocalizationComparison f V)
      (spacesRingedHom.relocalization c).toTopos.inverseImage ≫
    Functor.whiskerLeft ((spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((spacesEtalePullback f).obj V))
      (relocalizationInverseImageIso c).hom ≫
    Functor.whiskerLeft (spacesRingedToposHom f).toTopos.inverseImage
      (Functor.sheafPushforwardContinuousComp' (Over.mapForget c) (Type u)
        ((spacesEtaleTopology X).over U)
        ((spacesEtaleTopology X).over ((spacesEtalePullback f).obj V))
        (spacesEtaleTopology X)).hom

/-- Restricting the ambient sheaf and then relocalizing is restriction to the source slice. -/
@[expose]
def relocalizationOverIso {X : AlgebraicSpace S} {U V : spacesEtaleSite X} (c : U ⟶ V) :
    (spacesEtaleTopology X).overPullback (Type u) V ⋙
        (spacesRingedHom.relocalization c).toTopos.inverseImage ≅
      (spacesEtaleTopology X).overPullback (Type u) U :=
  Functor.isoWhiskerLeft ((spacesEtaleTopology X).overPullback (Type u) V)
      (relocalizationInverseImageIso c) ≪≫
    Functor.sheafPushforwardContinuousComp' (Over.mapForget c) (Type u)
      ((spacesEtaleTopology X).over U) ((spacesEtaleTopology X).over V) (spacesEtaleTopology X)

variable {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The spaces ambient comparison with both mk-object rebases included. -/
@[expose]
def rebasedSpacesComparison (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleTopology Y).overPullback (Type u) ((smallEtaleToSpaces Y).obj (smallEtaleSite.mk q)) ⋙
        (etaleRelocalizeSpacesLocalization p g f q hcomm).toTopos.inverseImage ⟶
      (spacesRingedToposHom f).toTopos.inverseImage ⋙
        (spacesEtaleTopology X).overPullback (Type u) ((smallEtaleToSpaces X).obj (smallEtaleSite.mk p)) :=
  Functor.whiskerRight (relocalizationOverIso (smallEtaleInclusion_mkIso q).inv).hom
      ((spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
          (spacesEtalePullbackLift p g f q hcomm)).toTopos.inverseImage ⋙
        (etaleRelocalizeMkRelocalization_source p).toTopos.inverseImage) ≫
    Functor.whiskerRight
      (spacesAtComparison f (spacesEtaleSite.mk q) (spacesEtalePullbackLift p g f q hcomm))
      (etaleRelocalizeMkRelocalization_source p).toTopos.inverseImage ≫
    Functor.whiskerLeft (spacesRingedToposHom f).toTopos.inverseImage
      (relocalizationOverIso (smallEtaleInclusion_mkIso p).hom).hom

/-- The actual ambient comparison for the chart presentation. -/
@[expose]
def smallAmbientComparison (hcomm : p ≫ f = g ≫ q) :
    (smallEtaleTopology Y).overPullback (Type u) (smallEtaleSite.mk q) ⋙
        (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ⟶
      (morphismOfTopoi f).inverseImage ⋙
        (smallEtaleTopology X).overPullback (Type u) (smallEtaleSite.mk p) :=
  Functor.whiskerRight (extensionOverIso Y (smallEtaleSite.mk q)).hom
      ((etaleRelocalizeSpacesLocalization p g f q hcomm).toTopos.inverseImage ⋙
        (smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.inverseImage) ≫
    Functor.whiskerLeft (EtaleTopos.siteEquivalence Y).inverse
      (Functor.whiskerRight (rebasedSpacesComparison p g f q hcomm)
        (smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.inverseImage) ≫
    Functor.whiskerLeft
      ((EtaleTopos.siteEquivalence Y).inverse ⋙ (spacesRingedToposHom f).toTopos.inverseImage)
      ((smallEtaleToSpaces X).sheafPushforwardOverPostComp (smallEtaleSite.mk p) (Type u)).hom ≫
    Functor.whiskerRight (morphismInverseImageIso f).hom
      ((smallEtaleTopology X).overPullback (Type u) (smallEtaleSite.mk p))

/-- The chart site's inverse image, transported by the concrete representable slice equivalences. -/
@[expose]
def slicePresentation (hcomm : p ≫ f = g ≫ q) :
    Over (etaleRepresentable (smallEtaleSite.mk q)) ⥤
      Over (etaleRepresentable (smallEtaleSite.mk p)) :=
  (etaleSliceEquivalence Y (smallEtaleSite.mk q)).inverse ⋙
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ⋙
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor

/-- The canonical ambient comparison on slices of small-site sheaves. -/
@[expose]
def sliceAmbientComparison (hcomm : p ≫ f = g ≫ q) :
    Over.star (etaleRepresentable (smallEtaleSite.mk q)) ⋙ slicePresentation p g f q hcomm ⟶
      (morphismOfTopoi f).inverseImage ⋙ Over.star (etaleRepresentable (smallEtaleSite.mk p)) :=
  Functor.whiskerRight (SubcanonicalSlice.starInverseIso (smallEtaleTopology Y) (smallEtaleSite.mk q)).hom
      ((etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ⋙
        (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor) ≫
    Functor.whiskerRight (smallAmbientComparison p g f q hcomm)
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor ≫
    Functor.whiskerLeft (morphismOfTopoi f).inverseImage
      (SubcanonicalSlice.restrictionIsoStar (smallEtaleTopology X) (smallEtaleSite.mk p)).hom

end AlgebraicGeometry.AlgebraicSpace.Relocalization


open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry


namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]
variable (hcomm : p ≫ f = g ≫ q)

/-- The first projection of the comparison: apply the ambient mate to the graph
of the given object over `h_V`, then project to the inverse image of its domain. -/
@[expose]
def comparisonLeft (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    ((slicePresentation p g f q hcomm).obj H).left ⟶
      (morphismOfTopoi f).inverseImage.obj H.left :=
  ((slicePresentation p g f q hcomm).map
      ((Over.forgetAdjStar (etaleRepresentable (smallEtaleSite.mk q))).unit.app H)).left ≫
    ((sliceAmbientComparison p g f q hcomm).app H.left).left ≫ prod.snd

/-- The constructed ambient mate sends the graph of a slice object over `h_V`
to the fibre over exactly the Lan/Yoneda parameter of the original square.
On representable sections this is the triangle of `spacesEtalePullbackLift`;
the two adjunction mates transport the same Lan unit used in the geometric parameter specification. -/
theorem comparisonLeft_comm (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    comparisonLeft p g f q hcomm H ≫ (morphismOfTopoi f).inverseImage.map H.hom =
      ((slicePresentation p g f q hcomm).obj H).hom ≫ etaleRelocalizeParameter p g f q hcomm :=
  sorry

/-- The graph square is cartesian. Indeed a slice object is the pullback of its
graph along the diagonal; localization preserves that finite limit, and the
ambient mate carries the diagonal to `etaleRelocalizeParameter`.
The cone's two maps are fixed by `comparisonLeft` and the original slice projection. -/
theorem comparisonSquare (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    IsPullback (comparisonLeft p g f q hcomm H)
      ((slicePresentation p g f q hcomm).obj H).hom
      ((morphismOfTopoi f).inverseImage.map H.hom) (etaleRelocalizeParameter p g f q hcomm) :=
  sorry

/-- The unique comparison to the specified pullback cone, over `h_U`.
Its inverse is the universal lift into the already specified cartesian cone;
no isomorphism is selected from a bare existence claim. -/
@[expose]
def comparisonObjIso (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    (slicePresentation p g f q hcomm).obj H ≅
      (etaleRelocalizeSliceInverseImage p g f q hcomm).obj H :=
  Over.isoMk (comparisonSquare p g f q hcomm H).isoPullback
    (comparisonSquare p g f q hcomm H).isoPullback_hom_snd

/-- The first pullback projection of the comparison is the ambient-mate construction. -/
theorem comparisonObjIso_hom_fst (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    (comparisonObjIso p g f q hcomm H).hom.left ≫
        pullback.fst ((morphismOfTopoi f).inverseImage.map H.hom)
          (etaleRelocalizeParameter p g f q hcomm) = comparisonLeft p g f q hcomm H :=
  (comparisonSquare p g f q hcomm H).isoPullback_hom_fst

/-- The second pullback projection of the comparison is the existing slice structure map. -/
theorem comparisonObjIso_hom_snd (H : Over (etaleRepresentable (smallEtaleSite.mk q))) :
    (comparisonObjIso p g f q hcomm H).hom.left ≫
        pullback.snd ((morphismOfTopoi f).inverseImage.map H.hom)
          (etaleRelocalizeParameter p g f q hcomm) =
      ((slicePresentation p g f q hcomm).obj H).hom :=
  (comparisonSquare p g f q hcomm H).isoPullback_hom_snd

/-- The pullback comparisons commute with arrows of the representable sheaf slice. -/
private theorem parameterInverseImageIso_naturality
    {A B : Over (etaleRepresentable (smallEtaleSite.mk q))} (k : A ⟶ B) :
    (slicePresentation p g f q hcomm).map k ≫ (comparisonObjIso p g f q hcomm B).hom =
      (comparisonObjIso p g f q hcomm A).hom ≫
        (etaleRelocalizeSliceInverseImage p g f q hcomm).map k := sorry

/-- The actual natural comparison with the inverse-image functor of representable localization at `s`. -/
@[expose]
def parameterInverseImageIso :
    slicePresentation p g f q hcomm ≅ etaleRelocalizeSliceInverseImage p g f q hcomm :=
  NatIso.ofComponents (comparisonObjIso p g f q hcomm)
    (by intro A B k; exact parameterInverseImageIso_naturality p g f q hcomm k)

/-- The representable-parameter inverse image presented back on the chart site slices. -/
@[expose]
def parameterSiteInverseImage :
    Sheaf ((smallEtaleTopology Y).over (smallEtaleSite.mk q)) (Type u) ⥤
      Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (Type u) :=
  (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
    etaleRelocalizeSliceInverseImage p g f q hcomm ⋙
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).inverse

/-- The chart inverse image is transported to the actual parameter inverse image,
using the two specified representable equivalences and the pullback comparison. -/
@[expose]
def parameterSiteInverseImageIso :
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage ≅
      parameterSiteInverseImage p g f q hcomm :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (etaleSliceEquivalence Y (smallEtaleSite.mk q)).unitIso _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor
      ((Functor.rightUnitor _).symm ≪≫
        Functor.isoWhiskerLeft
          ((etaleSliceEquivalence Y (smallEtaleSite.mk q)).inverse ⋙
            (etaleRelocalizeLocalization p g f q hcomm).toTopos.inverseImage)
          (etaleSliceEquivalence X (smallEtaleSite.mk p)).unitIso ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (parameterInverseImageIso p g f q hcomm)
          (etaleSliceEquivalence X (smallEtaleSite.mk p)).inverse)

end AlgebraicGeometry.AlgebraicSpace.Relocalization


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.GrothendieckTopology
open RingedSite.ToposHom


namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]
variable (hcomm : p ≫ f = g ≫ q)

/-- The explicit parameter inverse image is left exact, transported by the constructed iso. -/
instance parameterSiteInverseImage_preservesFiniteLimits :
    PreservesFiniteLimits (parameterSiteInverseImage p g f q hcomm) :=
  preservesFiniteLimits_of_natIso (parameterSiteInverseImageIso p g f q hcomm)

/-- The actual representable-parameter inverse image with its right adjoint. The latter is retained
from the site presentation, with adjunction transported through the constructed comparison. -/
@[expose]
def parameterMorphismOfTopoi :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u}
      ((smallEtaleTopology Y).over (smallEtaleSite.mk q))
      ((smallEtaleTopology X).over (smallEtaleSite.mk p)) where
  inverseImageFunctor := LeftExactFunctor.of (parameterSiteInverseImage p g f q hcomm)
  pushforward := (etaleRelocalizeLocalization p g f q hcomm).toTopos.pushforward
  adjunction := (etaleRelocalizeLocalization p g f q hcomm).toTopos.adjunction.ofNatIsoLeft
    (parameterSiteInverseImageIso p g f q hcomm)

/-- The existing direct-image ring map remains a ring map under the transported adjunction. -/
theorem parameterRingCompatible :
    @Direct.IsRingCompatible
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (parameterMorphismOfTopoi p g f q hcomm)
      (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImage
      (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImageForgetIso
      (etaleRelocalizeLocalization p g f q hcomm).directStructureMap := sorry

/-- The ringed representable-parameter localization at the actual sheaf map `s`, on the chart site slices. -/
@[expose]
def parameterRingedHom :
    RingedSite.ToposHom ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @ofDirectImage
    ((ringedSite X).localization (smallEtaleSite.mk p))
    ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
    (parameterMorphismOfTopoi p g f q hcomm)
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImage
    (etaleRelocalizeLocalization p g f q hcomm).toTopos.ringDirectImageForgetIso
    (etaleRelocalizeLocalization p g f q hcomm).directStructureMap
    (parameterRingCompatible p g f q hcomm)

/-- The new ringed-topos inverse image is definitionally the formula at `s` transported
by the specified representable-localization equivalences. -/
theorem parameterRingedHom_inverseImage :
    (parameterRingedHom p g f q hcomm).toTopos.inverseImage =
      (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
        ((morphismOfTopoi f).localization (etaleRepresentable (smallEtaleSite.mk q))).inverseImage ⋙
          Over.pullback (etaleRelocalizeParameter p g f q hcomm) ⋙
            (etaleSliceEquivalence X (smallEtaleSite.mk p)).inverse := rfl

/-- The direct-image comparison respects the structure-sheaf map. -/
private theorem parameterTwoIso_comm :
    (etaleRelocalizeLocalization p g f q hcomm).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans (Iso.refl ((etaleRelocalizeLocalization p g f q hcomm).toTopos.pushforward)).hom).app
        ((ringedSite X).localization (smallEtaleSite.mk p)).structureSheaf =
      (parameterRingedHom p g f q hcomm).directStructureMap := sorry

/-- The comparison on direct images is the identity because that actual right adjoint
was retained; the adjunction and inverse image were changed by the constructed comparison. -/
@[expose]
def parameterTwoIso :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeLocalization p g f q hcomm) (parameterRingedHom p g f q hcomm) where
  homIso := Iso.refl _
  comm := by exact parameterTwoIso_comm p g f q hcomm

/-- Representable localization sends the restricted structure object to the slice-product
structure object. This is the same comparison as on all ambient Type-u sheaves. -/
@[expose]
def structureObjectIso (Z : AlgebraicSpace S) (T : smallEtaleSite Z) :
    (etaleSliceEquivalence Z T).functor.obj
        (RingedSite.Hom.underlyingStructureSheaf ((ringedSite Z).localization T)) ≅
      (Over.star (etaleRepresentable T)).obj
        (RingedSite.Hom.underlyingStructureSheaf (ringedSite Z)) :=
  (SubcanonicalSlice.restrictionIsoStar (smallEtaleTopology Z) T).app
    (RingedSite.Hom.underlyingStructureSheaf (ringedSite Z))

/-- Transport of the actual parameter inverse image into the sheaf slice. -/
@[expose]
def parameterForgetIso :
    (parameterRingedHom p g f q hcomm).toTopos.inverseImage ⋙
        (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor ≅
      (etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
        etaleRelocalizeSliceInverseImage p g f q hcomm :=
  Functor.isoWhiskerLeft
      ((etaleSliceEquivalence Y (smallEtaleSite.mk q)).functor ⋙
        etaleRelocalizeSliceInverseImage p g f q hcomm)
      (etaleSliceEquivalence X (smallEtaleSite.mk p)).counitIso ≪≫ Functor.rightUnitor _

/-- The transported ring structure is the actual representable-parameter structure map at the same `s`.
This is a compatibility equation for already constructed maps, not an existence specification. -/
theorem parameterRingedHom_structure :
    (etaleSliceEquivalence X (smallEtaleSite.mk p)).functor.map
        (parameterRingedHom p g f q hcomm).underlyingMap ≫
      (structureObjectIso X (smallEtaleSite.mk p)).hom =
    (parameterForgetIso p g f q hcomm).hom.app
        (RingedSite.Hom.underlyingStructureSheaf ((ringedSite Y).localization (smallEtaleSite.mk q))) ≫
      (etaleRelocalizeSliceInverseImage p g f q hcomm).map
        (structureObjectIso Y (smallEtaleSite.mk q)).hom ≫
          etaleRelocalizeSliceStructureMap p g f q hcomm := sorry

end AlgebraicGeometry.AlgebraicSpace.Relocalization


open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace


namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The three actual direct-image comparisons: scheme identification, the retained
spaces comparison, and transport to the specified parameter inverse image. -/
@[expose]
def etaleRelocalizeIso_homIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugateScheme p g q).toTopos.pushforward ≅
      (Relocalization.parameterRingedHom p g f q hcomm).toTopos.pushforward :=
  (Relocalization.conjugateSchemeTwoIso p g f q hcomm).homIso ≪≫
    (etaleRelocalizeViaSpacesIso p g f q hcomm).homIso ≪≫
      (Relocalization.parameterTwoIso p g f q hcomm).homIso

/-- The small étale morphism conjugated by localization is two-isomorphic to localization at the geometric representable parameter. -/
@[expose]
def etaleRelocalizeIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugateScheme p g q)
      (Relocalization.parameterRingedHom p g f q hcomm) where
  homIso := etaleRelocalizeIso_homIso p g f q hcomm
  comm := by exact (((Relocalization.conjugateSchemeTwoIso p g f q hcomm).hom.comp
    (etaleRelocalizeViaSpacesIso p g f q hcomm).hom).comp
      (Relocalization.parameterTwoIso p g f q hcomm).hom).comm

/-- On every source-slice sheaf, the actual comparison is the three-factor pasting. -/
theorem etaleRelocalizeIso_homIso_app (hcomm : p ≫ f = g ≫ q)
    (F : Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (Type u)) :
    (etaleRelocalizeIso p g f q hcomm).homIso.hom.app F =
      (Relocalization.conjugateSchemeTwoIso p g f q hcomm).homIso.hom.app F ≫
        (etaleRelocalizeViaSpacesIso p g f q hcomm).homIso.hom.app F ≫
          (Relocalization.parameterTwoIso p g f q hcomm).homIso.hom.app F := rfl


end AlgebraicGeometry.AlgebraicSpace
