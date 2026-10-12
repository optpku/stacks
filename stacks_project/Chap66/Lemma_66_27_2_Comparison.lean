/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import stacks_project.Chap66.Lemma_66_27_1
public import stacks_project.Chap66.Lemma_66_27_2_Parameter
public import stacks_project.Chap66.Lemma_66_27_2_LocalizationAt

/-!
# Relocalization of morphisms of small-étale ringed topoi at schemes

A commutative square of algebraic spaces with étale scheme vertical arrows identifies the
small-étale morphism of `g` with the Modules-on-Sites localization of `f` at the induced
sheaf map `s`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The small-étale morphism of `g`, transported along the identifications
`(U_étale, 𝒪_U) ≅ localization of X at U` and
`(V_étale, 𝒪_V) ≅ localization of Y at V`. -/
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
def etaleRelocalizeMkRelocalization_source :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p)) :=
  spacesRingedHom.relocalization (smallEtaleInclusion_mkIso p).hom

/-- Relocalization along the inverse of `smallEtaleInclusion_mkIso q`. -/
def etaleRelocalizeMkRelocalization_target :
    RingedSite.ToposHom
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q))
      ((spacesRingedSite Y).localization
        ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) :=
  spacesRingedHom.relocalization (smallEtaleInclusion_mkIso q).inv

/-- The spaces-étale conjugate of `g`, transported from `spacesEtaleSite.mk` to the
small-étale inclusion images. -/
def etaleRelocalizeSpacesConjugate (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite Y).localization
        ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) :=
  @RingedSite.ToposHom.comp
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization
        ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) _ _ _
      (etaleRelocalizeMkRelocalization_source p)
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
          ((spacesRingedSite Y).localization (spacesEtaleSite.mk q))
          ((spacesRingedSite Y).localization
            ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) _ _ _
          (spacesEtaleRelocalizeConjugate p g f q hcomm)
          (etaleRelocalizeMkRelocalization_target q))

/-- The spaces-étale localization of `f` at `c`, transported from `spacesEtaleSite.mk` to the
small-étale inclusion images. -/
def etaleRelocalizeSpacesLocalization (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite Y).localization
        ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) :=
  @RingedSite.ToposHom.comp
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization
        ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) _ _ _
      (etaleRelocalizeMkRelocalization_source p)
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
          ((spacesRingedSite Y).localization (spacesEtaleSite.mk q))
          ((spacesRingedSite Y).localization
            ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q))) _ _ _
          (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
            (spacesEtalePullbackLift p g f q hcomm))
          (etaleRelocalizeMkRelocalization_target q))

/-- Direct-image comparison of the transported spaces-étale conjugate of `g` with the
transported spaces-étale localization of `f` at `c`. -/
def etaleRelocalizeSpacesBridge_homIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeSpacesConjugate p g f q hcomm).toTopos.pushforward ≅
      (etaleRelocalizeSpacesLocalization p g f q hcomm).toTopos.pushforward :=
  Functor.isoWhiskerLeft
      (etaleRelocalizeMkRelocalization_source p).toTopos.pushforward
      (Functor.isoWhiskerRight (spacesEtaleRelocalizeIso_homIso p g f q hcomm)
        (etaleRelocalizeMkRelocalization_target q).toTopos.pushforward)

/-- The small-étale morphism of `g`, transported to the localizations of `X` and `Y` by the
small-versus-spaces comparison and the identifications (66.27.0.2). -/
def etaleRelocalizeConjugate (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @RingedSite.ToposHom.comp
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
      (smallEtaleLocalizationComparison X (smallEtaleSite.mk p))
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization
            ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
          ((spacesRingedSite Y).localization
            ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q)))
          ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
          (etaleRelocalizeSpacesConjugate p g f q hcomm)
          (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)))

/-- The 18.22.3 localization of `f_small` at the parameter corresponding to `g`, presented by
conjugating the spaces-étale localization of Lemma 66.27.1 along the small-versus-spaces
comparisons. -/
def etaleRelocalizeLocalization (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) :=
  @RingedSite.ToposHom.comp
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((spacesRingedSite X).localization
        ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
      (smallEtaleLocalizationComparison X (smallEtaleSite.mk p))
      (@RingedSite.ToposHom.comp
          ((spacesRingedSite X).localization
            ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
          ((spacesRingedSite Y).localization
            ((smallEtaleInclusion Y).obj (smallEtaleSite.mk q)))
          ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _ _
          (etaleRelocalizeSpacesLocalization p g f q hcomm)
          (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)))

/-- Direct-image comparison of the untagged middle factor
`etaleRelocalizeConjugate` ≅ `etaleRelocalizeLocalization`. -/
def etaleRelocalizeViaSpacesIso_homIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugate p g f q hcomm).toTopos.pushforward ≅
      (etaleRelocalizeLocalization p g f q hcomm).toTopos.pushforward :=
  Functor.isoWhiskerLeft
      (smallEtaleLocalizationComparison X (smallEtaleSite.mk p)).toTopos.pushforward
      (Functor.isoWhiskerRight (etaleRelocalizeSpacesBridge_homIso p g f q hcomm)
        (smallEtaleLocalizationComparisonInv Y (smallEtaleSite.mk q)).toTopos.pushforward)

/-- Untagged middle factor identifying the spaces-route conjugate
`etaleRelocalizeConjugate` with the spaces-route localization
`etaleRelocalizeLocalization`. -/
def etaleRelocalizeViaSpacesIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugate p g f q hcomm)
      (etaleRelocalizeLocalization p g f q hcomm) where
  homIso := etaleRelocalizeViaSpacesIso_homIso p g f q hcomm
  comm := sorry

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

/-- The untagged middle-factor 2-cell as a morphism of ringed topoi. -/
def etaleRelocalizeViaSpacesIso_hom (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoMorphism
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugate p g f q hcomm)
      (etaleRelocalizeLocalization p g f q hcomm) :=
  (etaleRelocalizeViaSpacesIso p g f q hcomm).hom

/-- The untagged middle-factor 2-cell is invertible on its underlying direct-image
natural transformation. -/
instance etaleRelocalizeViaSpacesIso_homIso_isIso (hcomm : p ≫ f = g ≫ q) :
    IsIso (etaleRelocalizeViaSpacesIso p g f q hcomm).homIso.hom :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace
