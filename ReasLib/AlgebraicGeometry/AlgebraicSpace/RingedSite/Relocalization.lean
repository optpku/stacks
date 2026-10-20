module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PullbackLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.SpacesLocalization

/-! # Relocalization of spaces-étale ringed-topos morphisms

Commutative squares with étale vertical arrows identify conjugate morphisms with
localization at the canonical arrow into the base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V X Y : AlgebraicSpace S}
variable (p : U ⟶ X) (g : U ⟶ V) (f : X ⟶ Y) (q : V ⟶ Y)
variable [Etale p] [Etale q]

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
private def spacesEtaleRelocalizePalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) : AlgebraicSpace S :=
  pullback ((Over.post (spacesEtalePullback f)).obj W).hom.left
    (spacesEtalePullbackLift p g f q hcomm).left

/-- The structure morphism of the fibre product of `W ×_Y X` along `c`. -/
private def spacesEtaleRelocalizePalgHom (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    spacesEtaleRelocalizePalg p g f q hcomm W ⟶ X :=
  pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left
      (spacesEtalePullbackLift p g f q hcomm).left ≫ p

/-- The fibre product of `W ×_Y X` along `c` is étale over `X`. -/
private instance instEtale_spacesEtaleRelocalizePalgHom (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    Etale (spacesEtaleRelocalizePalgHom p g f q hcomm W) :=
  sorry

/-- The fibre product of `W ×_Y X` along `c`, as an object of `X_spaces,étale`. -/
private def spacesEtaleRelocalizePalgSite (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) : spacesEtaleSite X :=
  spacesEtaleSite.mk (spacesEtaleRelocalizePalgHom p g f q hcomm W)

/-- The projections to the two factors of the iterated base change agree over the base. -/
private theorem spacesEtaleRelocalizeToPalg_inner_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback.fst W.hom.left g) ≫ W.left.hom =
      (pullback.snd W.hom.left g ≫ p) ≫ f :=
  sorry

/-- The canonical map to the base change lies over the induced pullback arrow. -/
private theorem spacesEtaleRelocalizeToPalg_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback.lift (pullback.fst W.hom.left g)
      (pullback.snd W.hom.left g ≫ p) (spacesEtaleRelocalizeToPalg_inner_w p g f q hcomm W)) ≫ ((Over.post (spacesEtalePullback f)).obj W).hom.left =
      (pullback.snd W.hom.left g) ≫ (spacesEtalePullbackLift p g f q hcomm).left :=
  sorry

/-- The comparison from `W ×_V U` to the fibre product of `W ×_Y X` along `c`. -/
private def spacesEtaleRelocalizeToPalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    pullback W.hom.left g ⟶ spacesEtaleRelocalizePalg p g f q hcomm W :=
  pullback.lift
    (pullback.lift (pullback.fst W.hom.left g)
      (pullback.snd W.hom.left g ≫ p) (spacesEtaleRelocalizeToPalg_inner_w p g f q hcomm W))
    (pullback.snd W.hom.left g) (spacesEtaleRelocalizeToPalg_w p g f q hcomm W)

/-- The reverse comparison projections agree over the upper target. -/
private theorem spacesEtaleRelocalizeFromPalg_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left ≫ pullback.fst W.left.hom f) ≫ W.hom.left =
      (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) ≫ g :=
  sorry

/-- The comparison from the fibre product of `W ×_Y X` along `c` to `W ×_V U`. -/
private def spacesEtaleRelocalizeFromPalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    spacesEtaleRelocalizePalg p g f q hcomm W ⟶ pullback W.hom.left g :=
  pullback.lift
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left
        (spacesEtalePullbackLift p g f q hcomm).left ≫
      pullback.fst W.left.hom f)
    (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left
      (spacesEtalePullbackLift p g f q hcomm).left) (spacesEtaleRelocalizeFromPalg_w p g f q hcomm W)

/-- The first projection of the algebraic-space pullback commutes with its structure map. -/
private theorem spacesEtaleRelocalizePalgSiteLift_fst_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) ≫
        ((Over.post (spacesEtalePullback f)).obj W).left.hom =
      spacesEtaleRelocalizePalgHom p g f q hcomm W :=
  sorry

/-- The second projection of the algebraic-space pullback commutes with its structure map. -/
private theorem spacesEtaleRelocalizePalgSiteLift_snd_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) ≫ (spacesEtaleSite.mk p).hom =
      spacesEtaleRelocalizePalgHom p g f q hcomm W :=
  sorry

/-- The two projections in the étale site agree over their common target. -/
private theorem spacesEtaleRelocalizePalgSiteLift_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (MorphismProperty.Over.homMk
      (A := spacesEtaleRelocalizePalgSite p g f q hcomm W)
      (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) (spacesEtaleRelocalizePalgSiteLift_fst_w p g f q hcomm W)) ≫ ((Over.post (spacesEtalePullback f)).obj W).hom =
      (MorphismProperty.Over.homMk
      (A := spacesEtaleRelocalizePalgSite p g f q hcomm W)
      (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) (spacesEtaleRelocalizePalgSiteLift_snd_w p g f q hcomm W)) ≫ (spacesEtalePullbackLift p g f q hcomm) :=
  sorry

/-- The morphism in `X_spaces,étale` from the algebraic-space fibre product along `c`
to the created site pullback. -/
private def spacesEtaleRelocalizePalgSiteLift (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    spacesEtaleRelocalizePalgSite p g f q hcomm W ⟶
      pullback ((Over.post (spacesEtalePullback f)).obj W).hom
        (spacesEtalePullbackLift p g f q hcomm) :=
  pullback.lift
    (MorphismProperty.Over.homMk
      (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) (spacesEtaleRelocalizePalgSiteLift_fst_w p g f q hcomm W))
    (MorphismProperty.Over.homMk
      (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom.left (spacesEtalePullbackLift p g f q hcomm).left) (spacesEtaleRelocalizePalgSiteLift_snd_w p g f q hcomm W))
    (spacesEtaleRelocalizePalgSiteLift_w p g f q hcomm W)

/-- The underlying maps of the created pullback cone commute. -/
private theorem spacesEtaleRelocalizeSitePullbackToPalg_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom (spacesEtalePullbackLift p g f q hcomm)).left ≫ ((Over.post (spacesEtalePullback f)).obj W).hom.left =
      (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom (spacesEtalePullbackLift p g f q hcomm)).left ≫ (spacesEtalePullbackLift p g f q hcomm).left :=
  sorry

/-- The comparison from the created site pullback to the algebraic-space fibre product
along `c`. -/
private def spacesEtaleRelocalizeSitePullbackToPalg (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (pullback ((Over.post (spacesEtalePullback f)).obj W).hom
        (spacesEtalePullbackLift p g f q hcomm)).left ⟶
      spacesEtaleRelocalizePalg p g f q hcomm W :=
  pullback.lift
    (pullback.fst ((Over.post (spacesEtalePullback f)).obj W).hom
      (spacesEtalePullbackLift p g f q hcomm)).left
    (pullback.snd ((Over.post (spacesEtalePullback f)).obj W).hom
      (spacesEtalePullbackLift p g f q hcomm)).left
    (spacesEtaleRelocalizeSitePullbackToPalg_w p g f q hcomm W)

/-- The forward and reverse pullback comparisons compose to the identity. -/
private theorem spacesEtaleRelocalizeAssociator_hom_inv_id (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (eqToHom (spacesEtaleRelocalizeSiteLeft_obj_left_left p g f q hcomm W) ≫
      spacesEtaleRelocalizeToPalg p g f q hcomm W ≫
      (spacesEtaleRelocalizePalgSiteLift p g f q hcomm W).left ≫
      eqToHom (spacesEtaleRelocalizeSiteRight_obj_left_left p g f q hcomm W).symm) ≫
      (eqToHom (spacesEtaleRelocalizeSiteRight_obj_left_left p g f q hcomm W) ≫
      spacesEtaleRelocalizeSitePullbackToPalg p g f q hcomm W ≫
      spacesEtaleRelocalizeFromPalg p g f q hcomm W ≫
      eqToHom (spacesEtaleRelocalizeSiteLeft_obj_left_left p g f q hcomm W).symm) = 𝟙 _ :=
  sorry

/-- The reverse and forward pullback comparisons compose to the identity. -/
private theorem spacesEtaleRelocalizeAssociator_inv_hom_id (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (eqToHom (spacesEtaleRelocalizeSiteRight_obj_left_left p g f q hcomm W) ≫
      spacesEtaleRelocalizeSitePullbackToPalg p g f q hcomm W ≫
      spacesEtaleRelocalizeFromPalg p g f q hcomm W ≫
      eqToHom (spacesEtaleRelocalizeSiteLeft_obj_left_left p g f q hcomm W).symm) ≫
      (eqToHom (spacesEtaleRelocalizeSiteLeft_obj_left_left p g f q hcomm W) ≫
      spacesEtaleRelocalizeToPalg p g f q hcomm W ≫
      (spacesEtaleRelocalizePalgSiteLift p g f q hcomm W).left ≫
      eqToHom (spacesEtaleRelocalizeSiteRight_obj_left_left p g f q hcomm W).symm) = 𝟙 _ :=
  sorry

/-- The algebraic-space associator identifying `W ×_V U` with the created site pullback. -/
private def spacesEtaleRelocalizeAssociator (hcomm : p ≫ f = g ≫ q)
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
  hom_inv_id := spacesEtaleRelocalizeAssociator_hom_inv_id p g f q hcomm W
  inv_hom_id := spacesEtaleRelocalizeAssociator_inv_hom_id p g f q hcomm W

/-- The pullback associator commutes with the maps to the lower source. -/
private theorem spacesEtaleRelocalizeFunctorIsoApp_base_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (spacesEtaleRelocalizeAssociator p g f q hcomm W).hom ≫ ((spacesEtaleRelocalizeSiteRight p g f q hcomm).obj W).left.hom =
      ((spacesEtaleRelocalizeSiteLeft p g f q hcomm).obj W).left.hom :=
  sorry

/-- The pullback associator commutes with the slice structure arrows. -/
private theorem spacesEtaleRelocalizeFunctorIsoApp_slice_w (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (MorphismProperty.Over.isoMk (spacesEtaleRelocalizeAssociator p g f q hcomm W)
      (spacesEtaleRelocalizeFunctorIsoApp_base_w p g f q hcomm W)).hom ≫ ((spacesEtaleRelocalizeSiteRight p g f q hcomm).obj W).hom =
      ((spacesEtaleRelocalizeSiteLeft p g f q hcomm).obj W).hom :=
  sorry

-- Local declaration justification (metaprogramming implementation): Export the private
-- component for use in the exposed natural isomorphism without adding a public component API.
set_option backward.privateInPublic true in
/-- Objectwise pullback-associator isomorphism between the two site functors. -/
private def spacesEtaleRelocalizeFunctorIsoApp (hcomm : p ≫ f = g ≫ q)
    (W : Over (spacesEtaleSite.mk q)) :
    (spacesEtaleRelocalizeSiteLeft p g f q hcomm).obj W ≅
      (spacesEtaleRelocalizeSiteRight p g f q hcomm).obj W :=
  Over.isoMk
    (MorphismProperty.Over.isoMk (spacesEtaleRelocalizeAssociator p g f q hcomm W)
      (spacesEtaleRelocalizeFunctorIsoApp_base_w p g f q hcomm W))
    (spacesEtaleRelocalizeFunctorIsoApp_slice_w p g f q hcomm W)

/-- The component pullback comparisons commute with morphisms in the target slice. -/
private theorem spacesEtaleRelocalizeFunctorIso_naturality (hcomm : p ≫ f = g ≫ q)
    {W W' : Over (spacesEtaleSite.mk q)} (i : W ⟶ W') :
    (spacesEtaleRelocalizeSiteLeft p g f q hcomm).map i ≫
        (spacesEtaleRelocalizeFunctorIsoApp p g f q hcomm W').hom =
      (spacesEtaleRelocalizeFunctorIsoApp p g f q hcomm W).hom ≫
        (spacesEtaleRelocalizeSiteRight p g f q hcomm).map i :=
  sorry

-- Local declaration justification (metaprogramming implementation): The exposed natural
-- isomorphism uses a private component construction, keeping the pullback implementation private.
set_option backward.privateInPublic true in
/-- Pullback associator identifying the site functor of the conjugate of `g` with the site
functor of the localization of `f` at `c`. -/
def spacesEtaleRelocalizeFunctorIso (hcomm : p ≫ f = g ≫ q) :
    spacesEtaleRelocalizeSiteLeft p g f q hcomm ≅
      spacesEtaleRelocalizeSiteRight p g f q hcomm := by
  exact NatIso.ofComponents (spacesEtaleRelocalizeFunctorIsoApp p g f q hcomm)
    (fun i => by exact spacesEtaleRelocalizeFunctorIso_naturality p g f q hcomm i)

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
        (Over.Site.DirectImage.pullbackPresentation (spacesEtaleTopology X)
          (spacesEtalePullbackLift p g f q hcomm))
        ((Over.post (spacesEtalePullback f)).sheafPushforwardContinuous (Type u)
          ((spacesEtaleTopology Y).over (spacesEtaleSite.mk q))
          ((spacesEtaleTopology X).over
            ((spacesEtalePullback f).obj (spacesEtaleSite.mk q))))).symm

/-- The direct-image comparison respects the structure-sheaf maps. -/
private theorem spacesEtaleRelocalizeIso_comm (hcomm : p ≫ f = g ≫ q) :
    (spacesEtaleRelocalizeConjugate p g f q hcomm).directStructureMap ≫
        (MorphismOfTopoiIn.ringDirectImageNatTrans
          (spacesEtaleRelocalizeIso_homIso p g f q hcomm).hom).app
            ((spacesRingedSite X).localization (spacesEtaleSite.mk p)).structureSheaf =
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)).directStructureMap :=
  sorry

/-- The conjugate spaces-étale ringed-topos morphism is canonically 2-isomorphic to
localization along the induced arrow into the base change. -/
def spacesEtaleRelocalizeIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _
      (spacesEtaleRelocalizeConjugate p g f q hcomm)
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)) where
  homIso := spacesEtaleRelocalizeIso_homIso p g f q hcomm
  comm := by exact spacesEtaleRelocalizeIso_comm p g f q hcomm

/-- The forward comparison cell from the conjugate morphism to its localization. -/
def spacesEtaleRelocalizeIso_hom (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoMorphism
      ((spacesRingedSite X).localization (spacesEtaleSite.mk p))
      ((spacesRingedSite Y).localization (spacesEtaleSite.mk q)) _ _
      (spacesEtaleRelocalizeConjugate p g f q hcomm)
      (spacesRingedHom.localizationAt f (spacesEtaleSite.mk q)
        (spacesEtalePullbackLift p g f q hcomm)) :=
  (spacesEtaleRelocalizeIso p g f q hcomm).hom


end AlgebraicGeometry.AlgebraicSpace
