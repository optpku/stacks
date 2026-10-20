/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GeometricPointSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact
public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSheafSpace
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites

/-!
# Abelian geometric-point comparisons

Abelian sheaf fibres identify with geometric inverse image followed by the
identity-point fibre, evaluation, and global sections on the source-field spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology.Point
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open GeometricPoint

-- Local instance justification (defeq pin): the Abelian-induced preadditive and zero-morphism structures must agree with those used by right-derived global sections.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {Y : AlgebraicSpace S} (ybar : GeometricPoint Y)
variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion (ofOver ybar.overObj)).IsCoverDense
    (spacesEtaleTopology (ofOver ybar.overObj))]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1}]
variable [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u + 1} AddCommGrpCat.{u + 1}]
variable [hSmall : InitiallySmall.{u + 1}
    ((etaleBaseChange (X := ofOver ybar.overObj) ybar.hom ⋙
        (toSpacesEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [hAdj : Functor.IsRightAdjoint
    ((etaleBaseChange (X := ofOver ybar.overObj) ybar.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj)))]

/-- Abelian sheaf-fibre comparison of the stalk at `id ≫ ȳ` with the stalk at `ȳ`. -/
noncomputable def abelianImagePointStalkIso
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).sheafFiber.obj G ≅
      (toSmallEtalePoint ybar).sheafFiber.obj G := by
  refine
    { hom :=
        (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).presheafFiberDesc
          (fun U α ↦
            (toSmallEtalePoint ybar).toPresheafFiber U
              ((stalkFunctor_imagePoint_fiberHom ybar).app U α) G.obj)
          (fun _ _ _ _ ↦ ?_)
      inv :=
        (toSmallEtalePoint ybar).presheafFiberDesc
          (fun U α ↦
            (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).toPresheafFiber U
              ((stalkFunctor_imagePoint_fiberInv ybar).app U α) G.obj)
          (fun _ _ _ _ ↦ ?_)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- Comparison of the small étale sheaf fibre at the image of `idGeometricPoint ȳ` with
the comap fibre of the identity geometric point of `Spec κ(ȳ)` along `etaleBaseChange`. -/
noncomputable def abelianComapStalkCompare
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).sheafFiber.obj G ≅
      ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
          (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)).sheafFiber.obj G := by
  refine
    { hom :=
        (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).presheafFiberDesc
          (fun U α ↦
            ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
                (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)).toPresheafFiber U
              (smallLift_to_baseChangeLift ybar U α) G.obj)
          (fun _ _ _ _ ↦ ?_)
      inv :=
        ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
            (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)).presheafFiberDesc
          (fun U β ↦
            (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).toPresheafFiber U
              (baseChangeLift_to_smallLift ybar U β) G.obj)
          (fun _ _ _ _ ↦ ?_)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- Identity-point small étale sheaf fibre on `Spec κ(ȳ)` compared with evaluation on the
identity object. -/
noncomputable def uniquePointSheafFiberIsoEval :
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
          AddCommGrpCat.{u + 1}) ≅
      sheafToPresheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⋙
        (evaluation (smallEtaleSite (ofOver ybar.overObj))ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (idGeometricPoint_sourceObj ybar)) := by
  refine
    NatIso.ofComponents
      (fun G ↦
        { hom :=
            (toSmallEtalePoint (idGeometricPoint ybar)).presheafFiberDesc
              (fun U α ↦ G.obj.map (idGeometricPoint_siteHom ybar U α).op)
              (fun _ _ _ _ ↦ ?_)
          inv :=
            (toSmallEtalePoint (idGeometricPoint ybar)).toPresheafFiber
              (idGeometricPoint_sourceObj ybar) (idGeometricPoint_idLift ybar) G.obj
          hom_inv_id := ?_
          inv_hom_id := ?_ })
      (fun {_ _} _ ↦ ?_)
  all_goals sorry

/-- Identity-point spaces sheaf fibre on `Spec κ(ȳ)` compared with evaluation on the
spaces-étale identity object. -/
noncomputable def uniquePointSpacesSheafFiberIsoEval :
    ((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (spacesEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
          AddCommGrpCat.{u + 1}) ≅
      sheafToPresheaf (spacesEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⋙
        (evaluation (spacesEtaleSite (ofOver ybar.overObj))ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (idGeometricPoint_spacesSelf ybar)) := by
  refine
    NatIso.ofComponents
      (fun G ↦
        { hom :=
            (toSpacesEtalePoint (idGeometricPoint ybar)).presheafFiberDesc
              (fun V β ↦ G.obj.map (idGeometricPoint_spacesSiteHom ybar V β).op)
              (fun _ _ _ _ ↦ ?_)
          inv :=
            (toSpacesEtalePoint (idGeometricPoint ybar)).toPresheafFiber
              (idGeometricPoint_spacesSelf ybar) (idGeometricPoint_spacesIdLift ybar) G.obj
          hom_inv_id := ?_
          inv_hom_id := ?_ })
      (fun {_ _} _ ↦ ?_)
  all_goals sorry

/-- Pulling back by `ȳ → Y` produces the stalk: the abelian sheaf fibre of `G` at `ȳ`
identifies with the unique-point fibre of `ȳ⁻¹ G`. -/
noncomputable def abelianStalkPullbackIso
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSmallEtalePoint ybar).sheafFiber.obj G ≅
      (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).obj G) :=
  (abelianImagePointStalkIso ybar G).symm ≪≫
    abelianComapStalkCompare ybar G ≪≫
    (((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiberComapIsoOfMorphismOfSites
        (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom) AddCommGrpCat.{u + 1}).app G) ≪≫
    ((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber.mapIso
      ((Functor.sheafPullbackConstruction.sheafPullbackIso (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)
        AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
        (spacesEtaleTopology (ofOver ybar.overObj))).app G)) ≪≫
    ((uniquePointSpacesSheafFiberIsoEval ybar).app
      ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
          (spacesEtaleTopology (ofOver ybar.overObj))).obj G)) ≪≫
    (((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
          (spacesEtaleTopology (ofOver ybar.overObj))).obj G).obj.mapIso
      (idGeometricPoint_inclusionSelfIso ybar).op) ≪≫
    ((uniquePointSheafFiberIsoEval ybar).app
      ((sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).obj G)).symm

/-- The forward stalk-to-pullback comparison is the composite of the concrete
point transports, the inverse-image comparison, and the identity-point evaluations. -/
theorem abelianStalkPullbackIso_hom
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (abelianStalkPullbackIso ybar G).hom =
      (abelianImagePointStalkIso ybar G).inv ≫
        (abelianComapStalkCompare ybar G).hom ≫
        ((((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiberComapIsoOfMorphismOfSites
        (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom) AddCommGrpCat.{u + 1}).app G)).hom ≫
        (((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber.mapIso
      ((Functor.sheafPullbackConstruction.sheafPullbackIso (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)
        AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
        (spacesEtaleTopology (ofOver ybar.overObj))).app G))).hom ≫
        (((uniquePointSpacesSheafFiberIsoEval ybar).app
      ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
          (spacesEtaleTopology (ofOver ybar.overObj))).obj G))).hom ≫
        ((((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange (X := ofOver ybar.overObj) ybar.hom)
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
          (spacesEtaleTopology (ofOver ybar.overObj))).obj G).obj.mapIso
      (idGeometricPoint_inclusionSelfIso ybar).op)).hom ≫
        ((uniquePointSheafFiberIsoEval ybar).app
      ((sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).obj G)).inv :=
  sorry

/-- Evaluation of an abelian sheaf on the identity object of `Spec κ(ȳ)` compared with
`Hom(ℤ̲, -)`. -/
noncomputable def identityEvalIsoGlobalSections :
    (sheafToPresheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⋙
        (evaluation (smallEtaleSite (ofOver ybar.overObj))ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (idGeometricPoint_sourceObj ybar))) ≅
      globalSections (ofOver ybar.overObj) := by
  refine
    NatIso.ofComponents
      (fun G ↦
        { hom :=
            AddCommGrpCat.ofHom
              { toFun := fun s ↦
                  ((sheafificationAdjunction
                      (smallEtaleTopology (ofOver ybar.overObj))
                      AddCommGrpCat.{u + 1}).homEquiv
                    ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) G).symm
                    { app := fun V ↦
                        AddCommGrpCat.ofHom
                          { toFun := fun n ↦
                              n.down •
                                G.obj.map
                                  (smallEtaleSite.homToId ybar.overObj V.unop).op s
                            map_zero' := ?_
                            map_add' := ?_ }
                      naturality := fun _ _ _ ↦ ?_ }
                map_zero' := ?_
                map_add' := ?_ }
          inv :=
            AddCommGrpCat.ofHom
              { toFun := fun φ ↦
                  φ.hom.app (op (idGeometricPoint_sourceObj ybar))
                    (((sheafificationAdjunction
                            (smallEtaleTopology (ofOver ybar.overObj))
                            AddCommGrpCat.{u + 1}).unit.app
                        ((Functor.const _).obj
                          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                      (op (idGeometricPoint_sourceObj ybar)) (ULift.up (1 : ℤ)))
                map_zero' := ?_
                map_add' := ?_ }
          hom_inv_id := ?_
          inv_hom_id := ?_ })
      (fun {_ _} _ ↦ ?_)
  all_goals sorry

/-- Unique-point sheaf fibre on `Spec κ(ȳ)` compared with global sections `Hom(ℤ̲, -)`. -/
noncomputable def uniquePointSheafFiberIsoSections :
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
          AddCommGrpCat.{u + 1}) ≅
      globalSections (ofOver ybar.overObj) :=
  uniquePointSheafFiberIsoEval ybar ≪≫ identityEvalIsoGlobalSections ybar

end AlgebraicGeometry.AlgebraicSpace
