module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.BaseChange

/-!
# Geometric-point stalks and global sections

The stalk functor at a geometric point of an algebraic space is naturally isomorphic
to geometric inverse image followed by global sections on its source-field spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X)

/-- The identity geometric point of the source-field spectrum of a geometric point. -/
def idGeometricPoint : GeometricPoint (ofOver xbar.overObj) where
  K := xbar.K
  field := xbar.field
  structureHom := xbar.structureHom
  hom := 𝟙 (ofOver xbar.overObj)
  isAlgClosed := xbar.isAlgClosed

/-- The identity geometric point has the same source field as the original point. -/
@[simp]
theorem idGeometricPoint_K : (idGeometricPoint xbar).K = xbar.K :=
  sorry

/-- The identity geometric point has the original structure morphism to the base. -/
@[simp]
theorem idGeometricPoint_structureHom :
    (idGeometricPoint xbar).structureHom = xbar.structureHom :=
  sorry

/-- The morphism of the identity geometric point is the identity of its spectrum. -/
@[simp]
theorem idGeometricPoint_hom :
    (idGeometricPoint xbar).hom = 𝟙 (ofOver xbar.overObj) :=
  sorry

/-- Postcomposing the identity geometric point recovers the original morphism. -/
theorem idGeometricPoint_map_hom :
    ((idGeometricPoint xbar).map xbar.hom).hom = xbar.hom :=
  sorry

/-- Postcomposing the identity geometric point recovers the original image point. -/
theorem idGeometricPoint_map_image :
    ((idGeometricPoint xbar).map xbar.hom).image = xbar.image :=
  sorry

/-- The identity presentation object of the small étale site of the source-field spectrum. -/
def idGeometricPoint_sourceObj : smallEtaleSite (ofOver xbar.overObj) :=
  smallEtaleSite.mk (𝟙 (ofOver xbar.overObj))

/-- Global sections on the source-field spectrum, evaluated at its identity chart. -/
def idGeometricPoint_sections :
    Sheaf (smallEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafToPresheaf (smallEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⋙
    (evaluation (smallEtaleSite (ofOver xbar.overObj))ᵒᵖ (Type (u + 1))).obj
      (op (idGeometricPoint_sourceObj xbar))

/-- Geometric inverse image along a geometric point followed by global sections. -/
def pullbackThenSections :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1) :=
  (smallEtaleMorphismOfTopoi xbar.hom).inverseImage ⋙ idGeometricPoint_sections xbar

/-- Pullback followed by sections evaluates the inverse-image sheaf at the identity chart. -/
theorem pullbackThenSections_obj (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (pullbackThenSections xbar).obj F =
      ((smallEtaleMorphismOfTopoi xbar.hom).inverseImage.obj F).obj.obj
        (op (idGeometricPoint_sourceObj xbar)) :=
  sorry

/-- Transport lifts from the postcomposed identity point to the original geometric point,
preserving their underlying scheme morphisms. -/
def stalkFunctor_imagePoint_fiberHom :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber ⟶
      (toSmallEtalePoint xbar).fiber := by
  refine
    { app := fun U ↦ TypeCat.ofHom fun
        (α : OverLift ((idGeometricPoint xbar).map xbar.hom) U) ↦
          (OverLift.of α.hom ?_ : OverLift xbar U)
      naturality := ?_ }
  all_goals sorry

/-- Transport lifts to the postcomposed identity point, preserving their underlying
scheme morphisms. -/
def stalkFunctor_imagePoint_fiberInv :
    (toSmallEtalePoint xbar).fiber ⟶
      (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber := by
  refine
    { app := fun U ↦ TypeCat.ofHom fun (α : OverLift xbar U) ↦
        (OverLift.of α.hom ?_ : OverLift ((idGeometricPoint xbar).map xbar.hom) U)
      naturality := ?_ }
  all_goals sorry

/-- The sheaf fibres at a geometric point and its postcomposed identity point are isomorphic. -/
def stalkFunctor_imagePointIso (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).sheafFiber.obj F ≅
      (toSmallEtalePoint xbar).sheafFiber.obj F := by
  refine
    { hom := (Hom.sheafFiber ⟨stalkFunctor_imagePoint_fiberHom xbar⟩).app F
      inv := (Hom.sheafFiber ⟨stalkFunctor_imagePoint_fiberInv xbar⟩).app F
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- The identity scheme morphism lifts the identity geometric point through its identity chart. -/
def idGeometricPoint_idLift :
    (toSmallEtalePoint (idGeometricPoint xbar)).fiber.obj (idGeometricPoint_sourceObj xbar) :=
  OverLift.of (𝟙 xbar.overObj) (by sorry)

/-- A lift of the identity geometric point determines a morphism from the identity chart. -/
def idGeometricPoint_siteHom (U : smallEtaleSite (ofOver xbar.overObj))
    (α : (toSmallEtalePoint (idGeometricPoint xbar)).fiber.obj U) :
    idGeometricPoint_sourceObj xbar ⟶ U :=
  MorphismProperty.CostructuredArrow.homMk α.hom trivial (by sorry)

/-- The identity-point sheaf fibre is naturally isomorphic to global sections, by
restriction to the identity chart and the germ map there. -/
def idGeometricPoint_sheafFiber_iso_sections :
    ((toSmallEtalePoint (idGeometricPoint xbar)).sheafFiber :
        Sheaf (smallEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⥤ Type (u + 1)) ≅
      idGeometricPoint_sections xbar := by
  refine NatIso.ofComponents
    (fun G ↦
      { hom :=
          (toSmallEtalePoint (idGeometricPoint xbar)).presheafFiberDesc
            (fun U α ↦ G.obj.map (idGeometricPoint_siteHom xbar U α).op) ?_
        inv :=
          (toSmallEtalePoint (idGeometricPoint xbar)).toPresheafFiber
            (idGeometricPoint_sourceObj xbar) (idGeometricPoint_idLift xbar) G.obj
        hom_inv_id := ?_
        inv_hom_id := ?_ }) ?_
  all_goals sorry

/-- The identity object of the spaces étale site of the source-field spectrum. -/
def idGeometricPoint_spacesSelf : spacesEtaleSite (ofOver xbar.overObj) :=
  spacesEtaleSite.self (ofOver xbar.overObj)

/-- The identity morphism lifts the identity geometric point through the spaces-site identity. -/
def idGeometricPoint_spacesIdLift :
    (toSpacesEtalePoint (idGeometricPoint xbar)).fiber.obj
      (idGeometricPoint_spacesSelf xbar) :=
  Over.homMk (𝟙 (ofOver xbar.overObj)) (Category.id_comp _)

/-- A lift of the identity geometric point determines a spaces-site morphism from the identity. -/
def idGeometricPoint_spacesSiteHom (V : spacesEtaleSite (ofOver xbar.overObj))
    (β : (toSpacesEtalePoint (idGeometricPoint xbar)).fiber.obj V) :
    idGeometricPoint_spacesSelf xbar ⟶ V :=
  MorphismProperty.Over.homMk β.left (by sorry)

/-- On the spaces étale site, the identity-point fibre is evaluation at the identity object. -/
def idGeometricPoint_spacesSheafFiber_iso_sections :
    ((toSpacesEtalePoint (idGeometricPoint xbar)).sheafFiber :
        Sheaf (spacesEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⥤ Type (u + 1)) ≅
      sheafToPresheaf (spacesEtaleTopology (ofOver xbar.overObj)) (Type (u + 1)) ⋙
        (evaluation (spacesEtaleSite (ofOver xbar.overObj))ᵒᵖ (Type (u + 1))).obj
          (op (idGeometricPoint_spacesSelf xbar)) := by
  refine NatIso.ofComponents
    (fun G ↦
      { hom :=
          (toSpacesEtalePoint (idGeometricPoint xbar)).presheafFiberDesc
            (fun V β ↦ G.obj.map (idGeometricPoint_spacesSiteHom xbar V β).op) ?_
        inv :=
          (toSpacesEtalePoint (idGeometricPoint xbar)).toPresheafFiber
            (idGeometricPoint_spacesSelf xbar) (idGeometricPoint_spacesIdLift xbar) G.obj
        hom_inv_id := ?_
        inv_hom_id := ?_ }) ?_
  all_goals sorry

/-- The presentation inclusion sends the identity chart to the spaces-site identity object. -/
def idGeometricPoint_inclusionSelfIso :
    (smallEtaleToSpaces (ofOver xbar.overObj)).obj (idGeometricPoint_sourceObj xbar) ≅
      idGeometricPoint_spacesSelf xbar :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by sorry)

/-- Evaluation at the spaces-site identity agrees with evaluation at the included identity chart. -/
def idGeometricPoint_evalInclusionIso
    (G : Sheaf (spacesEtaleTopology (ofOver xbar.overObj)) (Type (u + 1))) :
    G.obj.obj (op (idGeometricPoint_spacesSelf xbar)) ≅
      G.obj.obj
        (op ((smallEtaleToSpaces (ofOver xbar.overObj)).obj
          (idGeometricPoint_sourceObj xbar))) :=
  G.obj.mapIso (idGeometricPoint_inclusionSelfIso xbar).op

/-- Étale base change to the source-field spectrum is a morphism of sites. -/
instance etaleBaseChange_hom_isMorphismOfSites :
    IsMorphismOfSites (smallEtaleTopology X)
      (spacesEtaleTopology (ofOver xbar.overObj)) (etaleBaseChange xbar.hom) :=
  sorry

/-- A scheme lift of the image point induces the universal lift through its étale base change. -/
def smallLift_to_baseChangeLift (U : smallEtaleSite X)
    (α : (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber.obj U) :
    (etaleLiftFunctor (idGeometricPoint xbar)).obj ((etaleBaseChange xbar.hom).obj U) := by
  refine Over.homMk
    (pullback.lift (𝟙 (yoneda.obj xbar.overObj)) (ofOverMap α.hom) ?_ :
      ofOver xbar.overObj ⟶ etaleBaseChangeSpace xbar.hom U) ?_
  all_goals sorry

/-- Projection from the étale base change recovers a scheme lift of the image point. -/
def baseChangeLift_to_smallLift (U : smallEtaleSite X)
    (β : (etaleLiftFunctor (idGeometricPoint xbar)).obj ((etaleBaseChange xbar.hom).obj U)) :
    (toSmallEtalePoint ((idGeometricPoint xbar).map xbar.hom)).fiber.obj U :=
  OverLift.of
    (Yoneda.fullyFaithful.preimage (β.left ≫ etaleBaseChangeSnd xbar.hom U)) (by sorry)

/-- The stalk at a geometric point identifies with sections of geometric inverse image
through image-point transport and the inverse-image stalk comparison. -/
def stalkFunctorIsoPullback_component (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (toSmallEtalePoint xbar).sheafFiber.obj F ≅ (pullbackThenSections xbar).obj F :=
  (stalkFunctor_imagePointIso xbar F).symm ≪≫
    (smallEtaleInverseImage_stalkIso xbar.hom (idGeometricPoint xbar) F).symm ≪≫
    (idGeometricPoint_sheafFiber_iso_sections xbar).app
      ((smallEtaleMorphismOfTopoi xbar.hom).inverseImage.obj F)

/-- The small étale stalk functor at a geometric point is naturally isomorphic to geometric
inverse image along that point followed by global sections on its source-field spectrum. -/
def stalkFunctorIsoPullback :
    ((toSmallEtalePoint xbar).sheafFiber :
        Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ Type (u + 1)) ≅
      pullbackThenSections xbar :=
  NatIso.ofComponents (fun F ↦ stalkFunctorIsoPullback_component xbar F)
    (by sorry)

/-- The components of the stalk-to-pullback natural isomorphism are the canonical comparisons. -/
theorem stalkFunctorIsoPullback_app (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (stalkFunctorIsoPullback xbar).app F = stalkFunctorIsoPullback_component xbar F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
