/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap66.Lemma_66_19_9_Stalk
public import stacks_project.Chap66.Remark_66_19_10_StalkFunctor

/-!
# Stalk functors as pullbacks along geometric points

The sheaf-level stalk functor `F ↦ F_xbar` on `Sh(X_étale)` is canonically isomorphic to
inverse image along the geometric-point morphism, followed by the identification of
`Sh(Spec k_étale)` with sets via the identity-point fibre (equivalently, global sections).
This is the algebraic-space analogue of Étale Cohomology, Remark 59.56.6, obtained from
Lemma 66.19.9 (4) at `f = xbar` together with Theorem 59.56.3 / Remark 59.56.6.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)

/-- The costructured arrow of the image of `idGeometricPoint xbar` along `xbar.hom`. -/
def idGeometricPoint_imageCostructuredArrow :
    CostructuredArrow (ofOverFunctor S) X :=
  CostructuredArrow.mk ((idGeometricPoint xbar).map xbar.hom).hom

/-- The costructured arrow of `xbar`. -/
def geometricPointCostructuredArrow :
    CostructuredArrow (ofOverFunctor S) X :=
  CostructuredArrow.mk xbar.hom

/-- The costructured-arrow identity comparing `idGeometricPoint xbar` postcomposed along
`xbar.hom` with `xbar`. -/
def idGeometricPoint_map_costructuredIso :
    idGeometricPoint_imageCostructuredArrow xbar ≅
      geometricPointCostructuredArrow xbar :=
  CostructuredArrow.isoMk (Iso.refl _) (Category.id_comp xbar.hom).symm

/-- Fibre map from the image-point fibre of `idGeometricPoint xbar` to the fibre of
`xbar`. -/
def stalkFunctor_imagePoint_fiberHom :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber ⟶
      (toSmallEtalePoint xbar).fiber :=
  Functor.whiskerLeft
    (MorphismProperty.CostructuredArrow.forget (@Etale S) ⊤ (ofOverFunctor S) X)
    (coyoneda.map (idGeometricPoint_map_costructuredIso xbar).inv.op)

/-- Fibre map from the fibre of `xbar` to the image-point fibre of
`idGeometricPoint xbar`. -/
def stalkFunctor_imagePoint_fiberInv :
    (toSmallEtalePoint xbar).fiber ⟶
      (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber :=
  Functor.whiskerLeft
    (MorphismProperty.CostructuredArrow.forget (@Etale S) ⊤ (ofOverFunctor S) X)
    (coyoneda.map (idGeometricPoint_map_costructuredIso xbar).hom.op)

/-- Transport of sheaf fibres along the identification of `xbar` with
`id_{Spec k} ≫ xbar`. -/
def stalkFunctor_imagePointIso (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).sheafFiber.obj F ≅
      (toSmallEtalePoint xbar).sheafFiber.obj F where
  hom := (Hom.sheafFiber ⟨stalkFunctor_imagePoint_fiberHom xbar⟩).app F
  inv := (Hom.sheafFiber ⟨stalkFunctor_imagePoint_fiberInv xbar⟩).app F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The identity object `Spec k` of the small étale site of the source of `xbar`. -/
def idGeometricPoint_sourceObj : smallEtaleSite (ofOver xbar.overObj) :=
  smallEtaleSite.mk (𝟙 (ofOver xbar.overObj))

/-- The identity lift of `idGeometricPoint xbar` through `Spec k`. -/
def idGeometricPoint_idLift :
    (toSmallEtalePoint (idGeometricPoint xbar)).fiber.obj (idGeometricPoint_sourceObj xbar) :=
  𝟙 _

/-- The morphism in the small étale site of `Spec k` from the identity object to `U` determined
by a lift of the identity geometric point. -/
def idGeometricPoint_siteHom (U : smallEtaleSite (ofOver xbar.overObj))
    (α : (toSmallEtalePoint (idGeometricPoint xbar)).fiber.obj U) :
    idGeometricPoint_sourceObj xbar ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk α.left trivial sorry

/-- The identity-point sheaf fibre on `Spec k` is evaluation on the identity object of the
small étale site, recovering the identification `Sh(Spec k_étale) = Sets` by global
sections. -/
def idGeometricPoint_sheafFiber_iso_sections :
    ((toSmallEtalePoint (idGeometricPoint xbar)).sheafFiber :
        Sheaf (smallEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⥤ Type (u + 1)) ≅
      sheafToPresheaf (smallEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⋙
        (evaluation (smallEtaleSite (ofOver xbar.overObj))ᵒᵖ (Type (u + 1))).obj
          (op (idGeometricPoint_sourceObj xbar)) :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          (toSmallEtalePoint (idGeometricPoint xbar)).presheafFiberDesc
            (fun U α ↦ G.obj.map (idGeometricPoint_siteHom xbar U α).op)
            (fun _ _ _ _ ↦ sorry)
        inv :=
          (toSmallEtalePoint (idGeometricPoint xbar)).toPresheafFiber
            (idGeometricPoint_sourceObj xbar) (idGeometricPoint_idLift xbar) G.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun {_ _} _ ↦ sorry)

/-- The identity object of the spaces étale site of `Spec k`. -/
def idGeometricPoint_spacesSelf : spacesEtaleSite (ofOver xbar.overObj) :=
  spacesEtaleSite.self (ofOver xbar.overObj)

/-- The identity lift of `idGeometricPoint xbar` through the spaces-étale identity object. -/
def idGeometricPoint_spacesIdLift :
    (toSpacesEtalePoint (idGeometricPoint xbar)).fiber.obj
      (idGeometricPoint_spacesSelf xbar) :=
  𝟙 _

/-- The morphism in the spaces étale site of `Spec k` from the identity object to `V`
determined by a lift of the identity geometric point. -/
def idGeometricPoint_spacesSiteHom (V : spacesEtaleSite (ofOver xbar.overObj))
    (β : (toSpacesEtalePoint (idGeometricPoint xbar)).fiber.obj V) :
    idGeometricPoint_spacesSelf xbar ⟶ V :=
  MorphismProperty.Over.homMk β.left sorry

/-- The identity-point spaces sheaf fibre on `Spec k` is evaluation on the identity object of
the spaces étale site. -/
def idGeometricPoint_spacesSheafFiber_iso_sections :
    ((toSpacesEtalePoint (idGeometricPoint xbar)).sheafFiber :
        Sheaf (spacesEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⥤ Type (u + 1)) ≅
      sheafToPresheaf (spacesEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⋙
        (evaluation (spacesEtaleSite (ofOver xbar.overObj))ᵒᵖ (Type (u + 1))).obj
          (op (idGeometricPoint_spacesSelf xbar)) :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          (toSpacesEtalePoint (idGeometricPoint xbar)).presheafFiberDesc
            (fun V β ↦ G.obj.map (idGeometricPoint_spacesSiteHom xbar V β).op)
            (fun _ _ _ _ ↦ sorry)
        inv :=
          (toSpacesEtalePoint (idGeometricPoint xbar)).toPresheafFiber
            (idGeometricPoint_spacesSelf xbar) (idGeometricPoint_spacesIdLift xbar) G.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun {_ _} _ ↦ sorry)

/-- The small étale identity object of `Spec k`, viewed in the spaces étale site, is the
spaces-étale identity object. -/
def idGeometricPoint_inclusionSelfIso :
    (smallEtaleInclusion (ofOver xbar.overObj)).obj (idGeometricPoint_sourceObj xbar) ≅
      idGeometricPoint_spacesSelf xbar :=
  MorphismProperty.Over.isoMk (Iso.refl _) sorry

/-- Evaluation of a spaces-étale sheaf on the identity object agrees with evaluation on the
image of the small étale identity object. -/
def idGeometricPoint_evalInclusionIso
    (G : Sheaf (spacesEtaleTopology (ofOver xbar.overObj)) (Type (u + 1))) :
    G.obj.obj (op (idGeometricPoint_spacesSelf xbar)) ≅
      G.obj.obj
        (op ((smallEtaleInclusion (ofOver xbar.overObj)).obj
          (idGeometricPoint_sourceObj xbar))) :=
  G.obj.mapIso (idGeometricPoint_inclusionSelfIso xbar).op

variable [∀ F : (smallEtaleSite X)ᵒᵖ ⥤ Type (u + 1),
    (etaleBaseChange xbar.hom).op.HasLeftKanExtension F]

/-- Étale base change along `xbar.hom` is a morphism of sites from the small étale site of `X`
to the spaces étale site of `Spec k`. -/
instance etaleBaseChange_hom_isMorphismOfSites :
    IsMorphismOfSites (smallEtaleTopology X)
      (spacesEtaleTopology (ofOver xbar.overObj)) (etaleBaseChange xbar.hom) :=
  sorry

variable [InitiallySmall
    ((etaleBaseChange xbar.hom ⋙
        (toSpacesEtalePoint (idGeometricPoint xbar)).fiber).Elements)]
variable [((etaleBaseChange xbar.hom).sheafPushforwardContinuous (Type (u + 1))
    (smallEtaleTopology X) (spacesEtaleTopology (ofOver xbar.overObj))).IsRightAdjoint]

/-- Convert a small étale lift of the image of `idGeometricPoint xbar` through `U` to a lift of
the identity geometric point through the base change `Spec k ×_X U`. -/
def smallLift_to_baseChangeLift (U : smallEtaleSite X)
    (α : (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber.obj U) :
    (etaleLiftFunctor (idGeometricPoint xbar)).obj ((etaleBaseChange xbar.hom).obj U) :=
  Over.homMk
    (pullback.lift (𝟙 (yoneda.obj xbar.overObj)) (ofOverMap α.left) sorry :
      ofOver xbar.overObj ⟶ etaleBaseChangeSpace xbar.hom U)
    sorry

/-- Convert a lift of the identity geometric point through the base change of `U` back to a
small étale lift of the image of `idGeometricPoint xbar`. -/
def baseChangeLift_to_smallLift (U : smallEtaleSite X)
    (β : (etaleLiftFunctor (idGeometricPoint xbar)).obj ((etaleBaseChange xbar.hom).obj U)) :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber.obj U :=
  CostructuredArrow.homMk
    (Yoneda.fullyFaithful.preimage (β.left ≫ etaleBaseChangeSnd xbar.hom U))
    sorry

/-- Inverse image along `etaleBaseChange xbar.hom` followed by the identity-point spaces
fibre, as the comap of the site-point comparison. -/
def inverseImage_comapIso (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    ((toSpacesEtalePoint (idGeometricPoint xbar)).comapOfMorphismOfSites
        (etaleBaseChange xbar.hom)).sheafFiber.obj F ≅
      (toSpacesEtalePoint (idGeometricPoint xbar)).sheafFiber.obj
        (((etaleBaseChange xbar.hom).sheafPullback (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology (ofOver xbar.overObj))).obj F) :=
  ((toSpacesEtalePoint (idGeometricPoint xbar)).sheafFiberComapIsoOfMorphismOfSites
      (etaleBaseChange xbar.hom) (Type (u + 1))).app F

/-- Comparison of the small étale sheaf fibre at the image of `idGeometricPoint xbar` with
the comap fibre of the identity geometric point of `Spec k` along `etaleBaseChange`. -/
def stalkFunctorIsoPullback_comapCompare (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).sheafFiber.obj F ≅
      ((toSpacesEtalePoint (idGeometricPoint xbar)).comapOfMorphismOfSites
          (etaleBaseChange xbar.hom)).sheafFiber.obj F where
  hom :=
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).presheafFiberDesc
      (fun U α ↦
        ((toSpacesEtalePoint (idGeometricPoint xbar)).comapOfMorphismOfSites
            (etaleBaseChange xbar.hom)).toPresheafFiber U
          (smallLift_to_baseChangeLift xbar U α) F.obj)
      (fun _ _ _ _ ↦ sorry)
  inv :=
    ((toSpacesEtalePoint (idGeometricPoint xbar)).comapOfMorphismOfSites
        (etaleBaseChange xbar.hom)).presheafFiberDesc
      (fun U β ↦
        (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).toPresheafFiber U
          (baseChangeLift_to_smallLift xbar U β) F.obj)
      (fun _ _ _ _ ↦ sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Abstract sheaf pullback along `etaleBaseChange` agrees with the Kan-extension
construction used by `sheafInverseImage`. -/
def stalkFunctorIsoPullback_pullbackSheafIso
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (((etaleBaseChange xbar.hom).sheafPullback (Type (u + 1))
        (smallEtaleTopology X) (spacesEtaleTopology (ofOver xbar.overObj))).obj F) ≅
      (Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange xbar.hom)
        (Type (u + 1)) (smallEtaleTopology X)
        (spacesEtaleTopology (ofOver xbar.overObj))).obj F :=
  (Functor.sheafPullbackConstruction.sheafPullbackIso (etaleBaseChange xbar.hom)
      (Type (u + 1)) (smallEtaleTopology X)
      (spacesEtaleTopology (ofOver xbar.overObj))).app F

/-- The identity-point spaces fibre of an étale-base-change pullback, compared with the
small étale identity-point fibre of `sheafInverseImage`. -/
def stalkFunctorIsoPullback_pullbackRestrict (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (toSpacesEtalePoint (idGeometricPoint xbar)).sheafFiber.obj
        (((etaleBaseChange xbar.hom).sheafPullback (Type (u + 1))
          (smallEtaleTopology X) (spacesEtaleTopology (ofOver xbar.overObj))).obj F) ≅
      (toSmallEtalePoint (idGeometricPoint xbar)).sheafFiber.obj
        ((sheafInverseImage (Type (u + 1)) xbar.hom).obj F) :=
  ((toSpacesEtalePoint (idGeometricPoint xbar)).sheafFiber.mapIso
      (stalkFunctorIsoPullback_pullbackSheafIso xbar F)).trans
    (((idGeometricPoint_spacesSheafFiber_iso_sections xbar).app
        ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange xbar.hom)
          (Type (u + 1)) (smallEtaleTopology X)
          (spacesEtaleTopology (ofOver xbar.overObj))).obj F)).trans
      ((idGeometricPoint_evalInclusionIso xbar
          ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange xbar.hom)
            (Type (u + 1)) (smallEtaleTopology X)
            (spacesEtaleTopology (ofOver xbar.overObj))).obj F)).trans
        ((idGeometricPoint_sheafFiber_iso_sections xbar).app
          ((sheafInverseImage (Type (u + 1)) xbar.hom).obj F)).symm))

/-- Component isomorphism identifying the stalk at `xbar` with inverse image followed by the
identity-point fibre, via Lemma 66.19.9 (4) at `f = xbar` and the comap comparison along
`etaleBaseChange`. -/
def stalkFunctorIsoPullback_component (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (toSmallEtalePoint xbar).sheafFiber.obj F ≅ (pullbackThenSections xbar).obj F :=
  (stalkFunctor_imagePointIso xbar F).symm.trans
    ((stalkFunctorIsoPullback_comapCompare xbar F).trans
      ((inverseImage_comapIso xbar F).trans
        (stalkFunctorIsoPullback_pullbackRestrict xbar F)))

/-- Remark 66.19.10: let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`xbar : Spec k ⟶ X` be a geometric point of `X`. By Étale Cohomology, Theorem 59.56.3 the
category of sheaves on `Spec k_étale` is equivalent to the category of sets (by taking a
sheaf to its global sections). Hence it follows from Lemma 66.19.9 (4) applied to the
morphism `xbar` that the functor `Sh(X_étale) ⥤ Sets`, `F ↦ F_xbar` is isomorphic to the
functor `Sh(X_étale) ⥤ Sh(Spec k_étale) = Sets`, `F ↦ xbar^* F`. Thus stalk functors may be
viewed as pullbacks along geometric morphisms, not merely the abstract morphisms of topoi
of Lemma 66.19.7. -/
@[stacks 04K3]
def stalkFunctorIsoPullback :
    ((toSmallEtalePoint xbar).sheafFiber :
        Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1)) ≅
      pullbackThenSections xbar :=
  NatIso.ofComponents (fun F ↦ stalkFunctorIsoPullback_component xbar F)
    (fun {_ _} _ ↦ sorry)

/-- Componentwise, `stalkFunctorIsoPullback` is `stalkFunctorIsoPullback_component`. -/
theorem stalkFunctorIsoPullback_app (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (stalkFunctorIsoPullback xbar).app F = stalkFunctorIsoPullback_component xbar F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
