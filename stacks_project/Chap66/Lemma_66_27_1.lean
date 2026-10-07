module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import stacks_project.Chap66.Lemma_66_27_1_BaseChange
public import stacks_project.Chap66.Lemma_66_27_1_Hom
public import stacks_project.Chap66.Lemma_66_27_1_LocalizationAt
public import stacks_project.Chap66.«66_27_0_1_Comparison»
public import stacks_project.Chap66.«66_27_0_2_Comparison»

/-!
# Relocalization of morphisms of spaces-étale ringed topoi

A commutative square of algebraic spaces with étale vertical arrows identifies the spaces-étale
morphism of `g` with the Modules-on-Sites localization of `f` at the induced arrow `c`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
variable (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
variable [Etale p] [Etale q]

/-- Continuous type-valued pushforward along `spacesEtaleLocalizationInverse` is a right
adjoint. -/
instance spacesEtaleLocalizationInverse_isRightAdjoint
    {Z W : AlgebraicSpace S} (e : Z ⟶ W) [Etale e] :
    ((spacesEtaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
      (spacesEtaleTopology Z)).IsRightAdjoint :=
  sorry

/-- The left adjoint of type-valued continuous pushforward along
`spacesEtaleLocalizationInverse` preserves finite limits. -/
instance instSpacesEtaleLocalizationInverse_leftAdjoint_preservesFiniteLimits
    {Z W : AlgebraicSpace S} (e : Z ⟶ W) [Etale e] :
    PreservesFiniteLimits
      ((spacesEtaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
        (spacesEtaleTopology Z)).leftAdjoint :=
  sorry

/-- Continuous type-valued pushforward along `spacesEtaleLocalizationFunctor` is a right
adjoint. -/
instance spacesEtaleLocalizationFunctor_isRightAdjoint
    {Z W : AlgebraicSpace S} (e : Z ⟶ W) [Etale e] :
    ((spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Z)
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))).IsRightAdjoint :=
  sorry

/-- The left adjoint of type-valued continuous pushforward along
`spacesEtaleLocalizationFunctor` preserves finite limits. -/
instance instSpacesEtaleLocalizationFunctor_leftAdjoint_preservesFiniteLimits
    {Z W : AlgebraicSpace S} (e : Z ⟶ W) [Etale e] :
    PreservesFiniteLimits
      ((spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z)
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))).leftAdjoint :=
  sorry

/-- The type-valued morphism of topoi presented by the forward spaces-étale localization
identification. -/
def spacesEtaleLocalizationIso_hom_morphismOfTopoi {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((spacesEtaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
        (spacesEtaleTopology Z)).leftAdjoint
  pushforward :=
    (spacesEtaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z)
  adjunction :=
    Adjunction.ofIsRightAdjoint
      ((spacesEtaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z))

/-- Coefficient-forgetful comparison for the forward spaces-étale localization identification. -/
def spacesEtaleLocalizationIso_hom_forgetIso {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    (spacesEtaleLocalizationInverse e).sheafPushforwardContinuous RingCat.{u}
          ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z) ⋙
        sheafCompose ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
          (forget RingCat.{u}) ≅
      sheafCompose (spacesEtaleTopology Z) (forget RingCat.{u}) ⋙
        (spacesEtaleLocalizationInverse e).sheafPushforwardContinuous (Type u)
          ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (spacesEtaleLocalizationInverse e)
      (forget RingCat.{u}) ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
      (spacesEtaleTopology Z))

/-- Direct-image ring compatibility of the forward spaces-étale localization identification. -/
theorem spacesEtaleLocalizationIso_hom_isRingCompatible {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    @Direct.IsRingCompatible (spacesRingedSite Z)
      ((spacesRingedSite W).localization (spacesEtaleSite.mk e)) _ _
      (spacesEtaleLocalizationIso_hom_morphismOfTopoi e)
      ((spacesEtaleLocalizationInverse e).sheafPushforwardContinuous RingCat.{u}
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z))
      (spacesEtaleLocalizationIso_hom_forgetIso e)
      (spacesEtaleLocalizationIso e).hom.structureSheafMap :=
  sorry

/-- The forward identification `(Z_spaces,étale, 𝒪_Z) ⟶ localization of W at Z` as a morphism
of ringed topoi. -/
def spacesEtaleLocalizationIso_hom_toToposHom {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    RingedSite.ToposHom (spacesRingedSite Z)
      ((spacesRingedSite W).localization (spacesEtaleSite.mk e)) :=
  @ofDirectImage (spacesRingedSite Z)
    ((spacesRingedSite W).localization (spacesEtaleSite.mk e)) _ _
    (spacesEtaleLocalizationIso_hom_morphismOfTopoi e)
    ((spacesEtaleLocalizationInverse e).sheafPushforwardContinuous RingCat.{u}
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) (spacesEtaleTopology Z))
    (spacesEtaleLocalizationIso_hom_forgetIso e)
    (spacesEtaleLocalizationIso e).hom.structureSheafMap
    (spacesEtaleLocalizationIso_hom_isRingCompatible e)

/-- The type-valued morphism of topoi presented by the inverse spaces-étale localization
identification. -/
def spacesEtaleLocalizationIso_inv_morphismOfTopoi {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u}
      (spacesEtaleTopology Z) ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) where
  inverseImageFunctor :=
    LeftExactFunctor.of
      ((spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z)
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))).leftAdjoint
  pushforward :=
    (spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
      (spacesEtaleTopology Z) ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
  adjunction :=
    Adjunction.ofIsRightAdjoint
      ((spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology Z) ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)))

/-- Coefficient-forgetful comparison for the inverse spaces-étale localization identification. -/
def spacesEtaleLocalizationIso_inv_forgetIso {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    (spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology Z)
          ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) ⋙
        sheafCompose (spacesEtaleTopology Z) (forget RingCat.{u}) ≅
      sheafCompose ((spacesEtaleTopology W).over (spacesEtaleSite.mk e))
          (forget RingCat.{u}) ⋙
        (spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous (Type u)
          (spacesEtaleTopology Z)
          ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)) :=
  eqToIso
    (Functor.sheafPushforwardContinuous.compSheafCompose (spacesEtaleLocalizationFunctor e)
      (forget RingCat.{u}) (spacesEtaleTopology Z)
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)))

/-- Direct-image ring compatibility of the inverse spaces-étale localization identification. -/
theorem spacesEtaleLocalizationIso_inv_isRingCompatible {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    @Direct.IsRingCompatible
      ((spacesRingedSite W).localization (spacesEtaleSite.mk e)) (spacesRingedSite Z) _ _
      (spacesEtaleLocalizationIso_inv_morphismOfTopoi e)
      ((spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology Z)
        ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)))
      (spacesEtaleLocalizationIso_inv_forgetIso e)
      (spacesEtaleLocalizationIso e).inv.structureSheafMap :=
  sorry

/-- The inverse identification `localization of W at Z ⟶ (Z_spaces,étale, 𝒪_Z)` as a morphism
of ringed topoi. -/
def spacesEtaleLocalizationIso_inv_toToposHom {Z W : AlgebraicSpace S} (e : Z ⟶ W)
    [Etale e] :
    RingedSite.ToposHom ((spacesRingedSite W).localization (spacesEtaleSite.mk e))
      (spacesRingedSite Z) :=
  @ofDirectImage ((spacesRingedSite W).localization (spacesEtaleSite.mk e))
    (spacesRingedSite Z) _ _
    (spacesEtaleLocalizationIso_inv_morphismOfTopoi e)
    ((spacesEtaleLocalizationFunctor e).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTopology Z)
      ((spacesEtaleTopology W).over (spacesEtaleSite.mk e)))
    (spacesEtaleLocalizationIso_inv_forgetIso e)
    (spacesEtaleLocalizationIso e).inv.structureSheafMap
    (spacesEtaleLocalizationIso_inv_isRingCompatible e)

/-- The spaces-étale morphism of `g`, transported along the identifications
`(U_spaces,étale, 𝒪_U) ≅ localization of X at U` and
`(V_spaces,étale, 𝒪_V) ≅ localization of Y at V`. -/
def spacesEtaleRelocalizeConjugate (hcomm : p ≫ f = g ≫ q) :
    RingedSite.ToposHom
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) :=
  @RingedSite.ToposHom.comp
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      (spacesRingedSite U)
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _ _
      (spacesEtaleLocalizationIso_inv_toToposHom p)
      (@RingedSite.ToposHom.comp (spacesRingedSite U) (spacesRingedSite V)
        ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _ _
        (spacesRingedToposHom g) (spacesEtaleLocalizationIso_hom_toToposHom q))

/-- The site functor of the conjugate of `g_spaces,étale`. -/
def spacesEtaleRelocalizeSiteLeft (hcomm : p ≫ f = g ≫ q) :
    Over (spacesEtaleSite.mk q) ⥤ Over (spacesEtaleSite.mk p) :=
  spacesEtaleLocalizationInverse q ⋙
    spacesEtalePullback g ⋙ spacesEtaleLocalizationFunctor p

/-- The site functor of the localization of `f_spaces,étale` at `c`. -/
def spacesEtaleRelocalizeSiteRight (hcomm : p ≫ f = g ≫ q) :
    Over (spacesEtaleSite.mk q) ⥤ Over (spacesEtaleSite.mk p) :=
  Over.post (spacesEtalePullback f) ⋙
    Over.Site.pullbackFunctor (spacesEtalePullbackLift p g f q hcomm)

/-- The conjugate site functor of `g` is continuous on spaces-étale slice topologies. -/
instance instIsContinuous_spacesEtaleRelocalizeSiteLeft (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleRelocalizeSiteLeft p g f q hcomm).IsContinuous
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk q))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) :=
  sorry

/-- The localization site functor of `f` at `c` is continuous on spaces-étale slice topologies. -/
instance instIsContinuous_spacesEtaleRelocalizeSiteRight (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleRelocalizeSiteRight p g f q hcomm).IsContinuous
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk q))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) :=
  sorry

/-- The underlying space of the conjugate site functor at `W` is `W ×_V U`. -/
theorem spacesEtaleRelocalizeSiteLeft_obj_left_left (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    ((spacesEtaleRelocalizeSiteLeft p g f q hcomm).obj W).left.left =
      pullback W.hom.left g :=
  rfl

/-- The underlying space of the localized site functor at `W` is the fibre product along `c`. -/
theorem spacesEtaleRelocalizeSiteRight_obj_left_left (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    ((spacesEtaleRelocalizeSiteRight p g f q hcomm).obj W).left.left =
      (pullback ((Over.post (spacesEtalePullback f)).obj W).hom
        (spacesEtalePullbackLift p g f q hcomm)).left :=
  rfl

/-- The algebraic-space fibre product of `W ×_Y X` along `c`. -/
def spacesEtaleRelocalizePalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) : AlgebraicSpace S :=
  pullback ((Over.post (spacesEtalePullback f)).obj W).hom.left
    (spacesEtalePullbackLift p g f q hcomm).left

/-- The structure morphism of the fibre product of `W ×_Y X` along `c`. -/
def spacesEtaleRelocalizePalgHom (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    spacesEtaleRelocalizePalg p g f q hcomm W ⟶ X :=
  pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left
      (spacesEtalePullbackLift p g f q hcomm).left ≫ p

/-- The fibre product of `W ×_Y X` along `c` is étale over `X`. -/
instance instEtale_spacesEtaleRelocalizePalgHom (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    Etale (spacesEtaleRelocalizePalgHom p g f q hcomm W) :=
  sorry

/-- The fibre product of `W ×_Y X` along `c`, as an object of `X_spaces,étale`. -/
def spacesEtaleRelocalizePalgSite (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) : spacesEtaleSite X :=
  spacesEtaleSite.mk (spacesEtaleRelocalizePalgHom p g f q hcomm W)

/-- The comparison from `W ×_V U` to the fibre product of `W ×_Y X` along `c`. -/
def spacesEtaleRelocalizeToPalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    pullback W.hom.left g ⟶ spacesEtaleRelocalizePalg p g f q hcomm W :=
  pullback.lift
    (pullback.lift (pullback.fst W.hom.left g)
      (pullback.snd W.hom.left g ≫ p) sorry)
    (pullback.snd W.hom.left g) sorry

/-- The comparison from the fibre product of `W ×_Y X` along `c` to `W ×_V U`. -/
def spacesEtaleRelocalizeFromPalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    spacesEtaleRelocalizePalg p g f q hcomm W ⟶ pullback W.hom.left g :=
  pullback.lift
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left
        (spacesEtalePullbackLift p g f q hcomm).left ≫
      pullback.fst W.left.hom f)
    (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left
      (spacesEtalePullbackLift p g f q hcomm).left) sorry

/-- The morphism in `X_spaces,étale` from the algebraic-space fibre product along `c`
to the created site pullback. -/
def spacesEtaleRelocalizePalgSiteLift (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    spacesEtaleRelocalizePalgSite p g f q hcomm W ⟶
      pullback ((Over.post (spacesEtalePullback f)).obj W).hom
        (spacesEtalePullbackLift p g f q hcomm) :=
  pullback.lift
    (MorphismProperty.Over.homMk
      (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left
        (spacesEtalePullbackLift p g f q hcomm).left) sorry)
    (MorphismProperty.Over.homMk
      (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left
        (spacesEtalePullbackLift p g f q hcomm).left) sorry)
    sorry

/-- The comparison from the created site pullback to the algebraic-space fibre product
along `c`. -/
def spacesEtaleRelocalizeSitePullbackToPalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback ((Over.post (spacesEtalePullback f)).obj W).hom
        (spacesEtalePullbackLift p g f q hcomm)).left ⟶
      spacesEtaleRelocalizePalg p g f q hcomm W :=
  pullback.lift
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom
      (spacesEtalePullbackLift p g f q hcomm)).left
    (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom
      (spacesEtalePullbackLift p g f q hcomm)).left
    sorry

/-- The algebraic-space associator identifying `W ×_V U` with the created site pullback. -/
def spacesEtaleRelocalizeAssociator (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    ((spacesEtaleRelocalizeSiteLeft p g f q hcomm).obj W).left.left ≅
      ((spacesEtaleRelocalizeSiteRight p g f q hcomm).obj W).left.left where
  hom :=
    eqToHom (spacesEtaleRelocalizeSiteLeft_obj_left_left p g f q hcomm W) ≫
      spacesEtaleRelocalizeToPalg p g f q hcomm W ≫
      (spacesEtaleRelocalizePalgSiteLift p g f q hcomm W).left ≫
      eqToHom (spacesEtaleRelocalizeSiteRight_obj_left_left p g f q hcomm W).symm
  inv :=
    eqToHom (spacesEtaleRelocalizeSiteRight_obj_left_left p g f q hcomm W) ≫
      spacesEtaleRelocalizeSitePullbackToPalg p g f q hcomm W ≫
      spacesEtaleRelocalizeFromPalg p g f q hcomm W ≫
      eqToHom (spacesEtaleRelocalizeSiteLeft_obj_left_left p g f q hcomm W).symm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Objectwise pullback-associator isomorphism between the two site functors. -/
def spacesEtaleRelocalizeFunctorIsoApp (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (spacesEtaleRelocalizeSiteLeft p g f q hcomm).obj W ≅
      (spacesEtaleRelocalizeSiteRight p g f q hcomm).obj W :=
  Over.isoMk
    (MorphismProperty.Over.isoMk (spacesEtaleRelocalizeAssociator p g f q hcomm W) sorry)
    sorry

/-- Pullback associator identifying the site functor of the conjugate of `g` with the site
functor of the localization of `f` at `c`. -/
def spacesEtaleRelocalizeFunctorIso (hcomm : p ≫ f = g ≫ q) :
    spacesEtaleRelocalizeSiteLeft p g f q hcomm ≅
      spacesEtaleRelocalizeSiteRight p g f q hcomm :=
  NatIso.ofComponents (spacesEtaleRelocalizeFunctorIsoApp p g f q hcomm) sorry

/-- Direct-image comparison between the conjugate of `g_spaces,étale` and the continuous
pullback presentation of the localization of `f_spaces,étale` at `c`. -/
def spacesEtaleRelocalizeIso_homIso (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleRelocalizeConjugate p g f q hcomm).toTopos.pushforward ≅
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)).toTopos.pushforward :=
  Functor.sheafPushforwardContinuousIso
      (spacesEtaleRelocalizeFunctorIso p g f q hcomm) (Type u)
      ((spacesEtaleTopology Y).over (spacesEtaleSite.mk q))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) ≪≫
    (Functor.isoWhiskerRight
        (spacesRingedHom.relocalizationPullbackPresentation
          (spacesEtalePullbackLift p g f q hcomm))
        ((Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
          ((spacesEtaleTopology Y).over (spacesEtaleSite.mk q))
          ((spacesEtaleTopology X).over
            ((spacesEtalePullback f).obj (spacesEtaleSite.mk q))))).symm

/-- Lemma 66.27.1: via the identifications (66.27.0.2) for `U ⟶ X` and `V ⟶ Y`, the morphism
of ringed topoi `(g_spaces,étale, g^♯)` is 2-isomorphic to the morphism
`(f_spaces,étale,c, f_c^♯)` constructed in Modules on Sites, Lemma 18.20.2 from
`(f_spaces,étale, f^♯)` and the map `c : U ⟶ V ×_Y X` corresponding to `g`. -/
@[stacks 04M4]
def spacesEtaleRelocalizeIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _
      (spacesEtaleRelocalizeConjugate p g f q hcomm)
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)) where
  homIso := spacesEtaleRelocalizeIso_homIso p g f q hcomm
  comm := sorry

/-- The comparison 2-cell of Lemma 66.27.1 as a morphism of ringed topoi. -/
def spacesEtaleRelocalizeIso_hom (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoMorphism
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _
      (spacesEtaleRelocalizeConjugate p g f q hcomm)
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)) :=
  (spacesEtaleRelocalizeIso p g f q hcomm).hom

/-- The comparison 2-cell of Lemma 66.27.1 is invertible on its underlying direct-image
natural transformation. -/
instance spacesEtaleRelocalizeIso_homIso_isIso (hcomm : p ≫ f = g ≫ q) :
    IsIso (spacesEtaleRelocalizeIso p g f q hcomm).homIso.hom :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace
