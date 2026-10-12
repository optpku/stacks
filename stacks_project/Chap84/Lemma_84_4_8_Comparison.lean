/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality.Iso
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact.Degree
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Homology
public import ReasLib.CategoryTheory.Sites.ConstantSheaf.Integer
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap66.Remark_66_19_10
public import stacks_project.Chap84.Lemma_84_4_8_Pullback
public import stacks_project.Chap84.Lemma_84_4_9_Comparison

/-!
# Stalk-to-fibre-cohomology comparisons for proper morphisms of algebraic spaces

Canonical comparison morphisms identifying the stalk of a higher direct image at a
geometric point with étale cohomology of the inverse image on the geometric fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits CategoryTheory.Sheaf
open CategoryTheory.GrothendieckTopology.Point
open CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open GeometricPoint

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Adjunction.Derived.Plus.right` / `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `smallEtaleDerivedBaseChangeHom` and right-derived comparisons.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
variable (f : X ⟶ Y) (ybar : GeometricPoint Y)

variable [(smallEtaleInclusion Y).IsCoverDense (spacesEtaleTopology Y)]
variable [(smallEtaleInclusion X).IsCoverDense (spacesEtaleTopology X)]
variable [(smallEtaleInclusion (ofOver ybar.overObj)).IsCoverDense
    (spacesEtaleTopology (ofOver ybar.overObj))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}]
variable [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [Abelian (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasInjectiveResolutions
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2} (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]
variable [(sheafPushforwardAbelian f).Additive]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar)).Additive]
variable [(sheafPushforwardAbelian f).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).PreservesHomology]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} (geometricFiberToX f ybar)).PreservesHomology]
variable [(sheafInverseImage AddCommGrpCat.{u + 1}
    (geometricFiberToX f ybar)).PreservesInjectiveObjects]
variable [(smallEtaleInverseExact (geometricFiberToX f ybar)).obj.PreservesInjectiveObjects]
variable [HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1}]
variable [HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u} AddCommGrpCat.{u + 1}]
variable [HasProducts.{u + 1} AddCommGrpCat.{u + 1}]
variable [InitiallySmall
    ((etaleBaseChange ybar.hom ⋙
        (toSpacesEtalePoint (idGeometricPoint ybar)).fiber).Elements)]
variable [((etaleBaseChange ybar.hom).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).IsRightAdjoint]

/-- Abelian sheaf-fibre comparison of the stalk at `id ≫ ȳ` with the stalk at `ȳ`. -/
noncomputable def abelianImagePointStalkIso
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).sheafFiber.obj G ≅
      (toSmallEtalePoint ybar).sheafFiber.obj G where
  hom :=
    (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).presheafFiberDesc
      (fun U α ↦
        (toSmallEtalePoint ybar).toPresheafFiber U
          ((stalkFunctor_imagePoint_fiberHom ybar).app U α) G.obj)
      (fun _ _ _ _ ↦ sorry)
  inv :=
    (toSmallEtalePoint ybar).presheafFiberDesc
      (fun U α ↦
        (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).toPresheafFiber U
          ((stalkFunctor_imagePoint_fiberInv ybar).app U α) G.obj)
      (fun _ _ _ _ ↦ sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Comparison of the small étale sheaf fibre at the image of `idGeometricPoint ȳ` with
the comap fibre of the identity geometric point of `Spec κ(ȳ)` along `etaleBaseChange`. -/
noncomputable def abelianComapStalkCompare
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).sheafFiber.obj G ≅
      ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
          (etaleBaseChange ybar.hom)).sheafFiber.obj G where
  hom :=
    (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).presheafFiberDesc
      (fun U α ↦
        ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
            (etaleBaseChange ybar.hom)).toPresheafFiber U
          (smallLift_to_baseChangeLift ybar U α) G.obj)
      (fun _ _ _ _ ↦ sorry)
  inv :=
    ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
        (etaleBaseChange ybar.hom)).presheafFiberDesc
      (fun U β ↦
        (toSmallEtalePoint ((idGeometricPoint ybar).map ybar.hom)).toPresheafFiber U
          (baseChangeLift_to_smallLift ybar U β) G.obj)
      (fun _ _ _ _ ↦ sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Inverse image along `etaleBaseChange ȳ` followed by the identity-point spaces fibre. -/
noncomputable def abelianInverseImageComapIso
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    ((toSpacesEtalePoint (idGeometricPoint ybar)).comapOfMorphismOfSites
        (etaleBaseChange ybar.hom)).sheafFiber.obj G ≅
      (toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        (((etaleBaseChange ybar.hom).sheafPullback AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).obj G) :=
  ((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiberComapIsoOfMorphismOfSites
      (etaleBaseChange ybar.hom) AddCommGrpCat.{u + 1}).app G

/-- Identity-point small étale sheaf fibre on `Spec κ(ȳ)` compared with evaluation on the
identity object. -/
noncomputable def uniquePointSheafFiberIsoEval :
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
          AddCommGrpCat.{u + 1}) ≅
      sheafToPresheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⋙
        (evaluation (smallEtaleSite (ofOver ybar.overObj))ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (idGeometricPoint_sourceObj ybar)) :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          (toSmallEtalePoint (idGeometricPoint ybar)).presheafFiberDesc
            (fun U α ↦ G.obj.map (idGeometricPoint_siteHom ybar U α).op)
            (fun _ _ _ _ ↦ sorry)
        inv :=
          (toSmallEtalePoint (idGeometricPoint ybar)).toPresheafFiber
            (idGeometricPoint_sourceObj ybar) (idGeometricPoint_idLift ybar) G.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun {_ _} _ ↦ sorry)

/-- Identity-point spaces sheaf fibre on `Spec κ(ȳ)` compared with evaluation on the
spaces-étale identity object. -/
noncomputable def uniquePointSpacesSheafFiberIsoEval :
    ((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (spacesEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
          AddCommGrpCat.{u + 1}) ≅
      sheafToPresheaf (spacesEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⋙
        (evaluation (spacesEtaleSite (ofOver ybar.overObj))ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (idGeometricPoint_spacesSelf ybar)) :=
  NatIso.ofComponents
    (fun G ↦
      { hom :=
          (toSpacesEtalePoint (idGeometricPoint ybar)).presheafFiberDesc
            (fun V β ↦ G.obj.map (idGeometricPoint_spacesSiteHom ybar V β).op)
            (fun _ _ _ _ ↦ sorry)
        inv :=
          (toSpacesEtalePoint (idGeometricPoint ybar)).toPresheafFiber
            (idGeometricPoint_spacesSelf ybar) (idGeometricPoint_spacesIdLift ybar) G.obj
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun {_ _} _ ↦ sorry)

/-- Evaluation of a spaces-étale abelian sheaf on the identity object agrees with evaluation
on the image of the small étale identity object. -/
noncomputable def uniquePointEvalInclusionIso
    (G : Sheaf (spacesEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}) :
    G.obj.obj (op (idGeometricPoint_spacesSelf ybar)) ≅
      G.obj.obj
        (op ((smallEtaleInclusion (ofOver ybar.overObj)).obj
          (idGeometricPoint_sourceObj ybar))) :=
  G.obj.mapIso (idGeometricPoint_inclusionSelfIso ybar).op

/-- Abstract sheaf pullback along `etaleBaseChange` agrees with the Kan-extension
construction used by `sheafInverseImage`. -/
noncomputable def abelianPullbackSheafIso
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (((etaleBaseChange ybar.hom).sheafPullback AddCommGrpCat.{u + 1}
        (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).obj G) ≅
      (Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange ybar.hom)
        AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
        (spacesEtaleTopology (ofOver ybar.overObj))).obj G :=
  (Functor.sheafPullbackConstruction.sheafPullbackIso (etaleBaseChange ybar.hom)
      AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
      (spacesEtaleTopology (ofOver ybar.overObj))).app G

/-- The identity-point spaces fibre of an étale-base-change pullback, compared with the
small étale identity-point fibre of `sheafInverseImage`. -/
noncomputable def abelianPullbackRestrict
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        (((etaleBaseChange ybar.hom).sheafPullback AddCommGrpCat.{u + 1}
          (smallEtaleTopology Y) (spacesEtaleTopology (ofOver ybar.overObj))).obj G) ≅
      (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).obj G) :=
  ((toSpacesEtalePoint (idGeometricPoint ybar)).sheafFiber.mapIso
      (abelianPullbackSheafIso ybar G)).trans
    (((uniquePointSpacesSheafFiberIsoEval ybar).app
        ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange ybar.hom)
          AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
          (spacesEtaleTopology (ofOver ybar.overObj))).obj G)).trans
      ((uniquePointEvalInclusionIso ybar
          ((Functor.sheafPullbackConstruction.sheafPullback (etaleBaseChange ybar.hom)
            AddCommGrpCat.{u + 1} (smallEtaleTopology Y)
            (spacesEtaleTopology (ofOver ybar.overObj))).obj G)).trans
        ((uniquePointSheafFiberIsoEval ybar).app
          ((sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).obj G)).symm))

/-- Pulling back by `ȳ → Y` produces the stalk: the abelian sheaf fibre of `G` at `ȳ`
identifies with the unique-point fibre of `ȳ⁻¹ G`. -/
noncomputable def abelianStalkPullbackIso
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (toSmallEtalePoint ybar).sheafFiber.obj G ≅
      (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).obj G) :=
  (abelianImagePointStalkIso ybar G).symm ≪≫
    abelianComapStalkCompare ybar G ≪≫
      abelianInverseImageComapIso ybar G ≪≫
        abelianPullbackRestrict ybar G

/-- Forward map of `abelianStalkPullbackIso`. -/
theorem abelianStalkPullbackIso_hom
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (abelianStalkPullbackIso ybar G).hom =
      (abelianImagePointStalkIso ybar G).inv ≫
        (abelianComapStalkCompare ybar G).hom ≫
          (abelianInverseImageComapIso ybar G).hom ≫
            (abelianPullbackRestrict ybar G).hom :=
  sorry

/-- Evaluation of an abelian sheaf on the identity object of `Spec κ(ȳ)` compared with
`Hom(ℤ̲, -)`. -/
noncomputable def identityEvalIsoGlobalSections :
    (sheafToPresheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⋙
        (evaluation (smallEtaleSite (ofOver ybar.overObj))ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (idGeometricPoint_sourceObj ybar))) ≅
      globalSections (ofOver ybar.overObj) :=
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
                          map_zero' := sorry
                          map_add' := sorry }
                    naturality := fun _ _ _ ↦ sorry }
              map_zero' := sorry
              map_add' := sorry }
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
              map_zero' := sorry
              map_add' := sorry }
        hom_inv_id := sorry
        inv_hom_id := sorry })
    (fun {_ _} _ ↦ sorry)

/-- Unique-point sheaf fibre on `Spec κ(ȳ)` compared with global sections `Hom(ℤ̲, -)`. -/
noncomputable def uniquePointSheafFiberIsoSections :
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
        Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
          AddCommGrpCat.{u + 1}) ≅
      globalSections (ofOver ybar.overObj) :=
  uniquePointSheafFiberIsoEval ybar ≪≫ identityEvalIsoGlobalSections ybar

/-- Global sections on `Spec κ(ȳ)` of a pushforward along the fibre structure morphism
identify with global sections on the geometric fibre. -/
noncomputable def geometricFiberPushforwardSectionsIso :
    sheafPushforwardAbelian (geometricFiberToPoint f ybar) ⋙
        globalSections (ofOver ybar.overObj) ≅
      globalSections (geometricFiber f ybar) :=
  NatIso.ofComponents
    (fun G ↦ homConstantPushforwardIso (geometricFiberToPoint f ybar) G)
    (fun {_ _} _ ↦ sorry)

variable [(sheafInverseImage AddCommGrpCat.{u + 1} ybar.hom).PreservesInjectiveObjects]
variable [(globalSections (ofOver ybar.overObj)).Additive]
variable [(globalSections (ofOver ybar.overObj)).PreservesHomology]
variable [(globalSections (geometricFiber f ybar)).Additive]
variable [(sheafPushforwardAbelian (geometricFiberToPoint f ybar) ⋙
    globalSections (ofOver ybar.overObj)).Additive]
variable [(globalSections (geometricFiber f ybar)).toBoundedBelowDerived.HasRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))]
variable [((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1}).Additive]
variable [((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
    Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1}).PreservesHomology]
variable [PreservesFiniteLimits
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
        AddCommGrpCat.{u + 1})]
variable [PreservesFiniteColimits
    ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
      Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
        AddCommGrpCat.{u + 1})]
variable [EnoughInjectives (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives
    (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1})]
variable [EnoughInjectives
    (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})]

/-- Degree-`n` proper base-change comparison of `f` along the geometric fibre square. -/
noncomputable abbrev higherDirectImage_baseChangeHom_geometricFiber
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :=
  higherDirectImage_baseChangeHom f ybar.hom
    (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
    (geometricFiber_isPullback f ybar) F n

/-- Canonical comparison `(R^n f_* F)_ȳ ⟶ H^n_étale(X_ȳ, F_ȳ)` of abelian groups. -/
noncomputable def higherDirectImageStalkToGeometricFiberCohomology
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        (((sheafPushforwardAbelian f).rightDerived n).obj F) ⟶
      etaleCohomology (geometricFiber f ybar) (geometricFiberAbelianSheaf f ybar F) n :=
  (abelianStalkPullbackIso ybar
      (((sheafPushforwardAbelian f).rightDerived n).obj F)).hom ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((Functor.RightDerived.postcompExactIso (sheafPushforwardAbelian f)
          (smallEtaleInverseExact ybar.hom) n).inv.app F) ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      (higherDirectImage_baseChangeHom_geometricFiber f ybar F n) ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((Functor.RightDerived.precompExactIso
          (smallEtaleInverseExact (geometricFiberToX f ybar))
          (sheafPushforwardAbelian (geometricFiberToPoint f ybar)) n).hom.app F) ≫
    (uniquePointSheafFiberIsoSections ybar).hom.app
      (((sheafPushforwardAbelian (geometricFiberToPoint f ybar)).rightDerived n).obj
        (geometricFiberAbelianSheaf f ybar F)) ≫
    (Functor.RightDerived.postcompIso
        (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
        (globalSections (ofOver ybar.overObj)) n).inv.app
      (geometricFiberAbelianSheaf f ybar F) ≫
    (NatIso.rightDerived (geometricFiberPushforwardSectionsIso f ybar) n).hom.app
      (geometricFiberAbelianSheaf f ybar F)

/-- `higherDirectImageStalkToGeometricFiberCohomology` is the composite of abelian
stalk-pullback, the degree-`n` proper base-change comparison on `ȳ ×_Y X`, and the
unique-point identification of `R^n f'_*` with étale cohomology of the fibre. -/
theorem higherDirectImageStalkToGeometricFiberCohomology_eq
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (n : ℕ) :
    higherDirectImageStalkToGeometricFiberCohomology f ybar F n =
      (abelianStalkPullbackIso ybar
          (((sheafPushforwardAbelian f).rightDerived n).obj F)).hom ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((Functor.RightDerived.postcompExactIso (sheafPushforwardAbelian f)
              (smallEtaleInverseExact ybar.hom) n).inv.app F) ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          (higherDirectImage_baseChangeHom_geometricFiber f ybar F n) ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((Functor.RightDerived.precompExactIso
              (smallEtaleInverseExact (geometricFiberToX f ybar))
              (sheafPushforwardAbelian (geometricFiberToPoint f ybar)) n).hom.app F) ≫
        (uniquePointSheafFiberIsoSections ybar).hom.app
          (((sheafPushforwardAbelian (geometricFiberToPoint f ybar)).rightDerived n).obj
            (geometricFiberAbelianSheaf f ybar F)) ≫
        (Functor.RightDerived.postcompIso
            (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
            (globalSections (ofOver ybar.overObj)) n).inv.app
          (geometricFiberAbelianSheaf f ybar F) ≫
        (NatIso.rightDerived (geometricFiberPushforwardSectionsIso f ybar) n).hom.app
          (geometricFiberAbelianSheaf f ybar F) :=
  rfl

/-- Identification of the unique-point fibre of derived pushforward homology with étale
cohomology of a bounded-below complex on the geometric fibre. -/
noncomputable def derivedUniquePointHomologyIsoFibreCohomology
    (E' : DerivedCategory.Plus
      (Sheaf (smallEtaleTopology (geometricFiber f ybar)) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}) n).obj
          ((smallEtaleDerivedPushforward (geometricFiberToPoint f ybar)).obj E')) ≅
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        (DerivedCategory.Plus.ι.obj
          ((Functor.RightDerived.Bounded.functor
              (globalSections (geometricFiber f ybar))).obj E')) :=
  (ExactFunctor.Derived.Plus.homologyIso
      (ExactFunctor.of
        ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
          Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
            AddCommGrpCat.{u + 1}))
      ((smallEtaleDerivedPushforward (geometricFiberToPoint f ybar)).obj E') n).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).mapIso
      ((ExactSecond.iso (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
          (ExactFunctor.of
            ((toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber :
              Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1} ⥤
                AddCommGrpCat.{u + 1}))).app E') ≪≫
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} n).mapIso
      ((Functor.RightDerived.Bounded.mapIso
          (Functor.isoWhiskerLeft (sheafPushforwardAbelian (geometricFiberToPoint f ybar))
              (uniquePointSheafFiberIsoSections ybar) ≪≫
            geometricFiberPushforwardSectionsIso f ybar)).app E')

/-- Canonical comparison `(R^n f_* E)_ȳ ⟶ H^n_étale(X_ȳ, E_ȳ)` of abelian groups. -/
noncomputable def derivedHigherDirectImageStalkToGeometricFiberCohomology
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    (toSmallEtalePoint ybar).sheafFiber.obj
        ((DerivedCategory.homologyFunctor
            (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) n).obj
          (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedPushforward f).obj E))) ⟶
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        (DerivedCategory.Plus.ι.obj
          ((Functor.RightDerived.Bounded.functor
              (globalSections (geometricFiber f ybar))).obj
            (geometricFiberDerived f ybar E))) :=
  (abelianStalkPullbackIso ybar
      ((DerivedCategory.homologyFunctor
          (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) n).obj
        (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedPushforward f).obj E)))).hom ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((ExactFunctor.Derived.Plus.homologyIso (smallEtaleInverseExact ybar.hom)
          ((smallEtaleDerivedPushforward f).obj E) n).inv) ≫
    (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1}) n).map
        (smallEtaleDerivedBaseChangeHom f ybar.hom
          (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
          (geometricFiber_isPullback f ybar) E)) ≫
    (derivedUniquePointHomologyIsoFibreCohomology f ybar
        (geometricFiberDerived f ybar E) n).hom

/-- `derivedHigherDirectImageStalkToGeometricFiberCohomology` is assembled from abelian
stalk-pullback, derived proper base change, and derived fibre sections. -/
theorem derivedHigherDirectImageStalkToGeometricFiberCohomology_eq
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (n : ℤ) :
    derivedHigherDirectImageStalkToGeometricFiberCohomology f ybar E n =
      (abelianStalkPullbackIso ybar
          ((DerivedCategory.homologyFunctor
              (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) n).obj
            (DerivedCategory.Plus.ι.obj ((smallEtaleDerivedPushforward f).obj E)))).hom ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((ExactFunctor.Derived.Plus.homologyIso (smallEtaleInverseExact ybar.hom)
              ((smallEtaleDerivedPushforward f).obj E) n).inv) ≫
        (toSmallEtalePoint (idGeometricPoint ybar)).sheafFiber.map
          ((DerivedCategory.Plus.homologyFunctor
              (Sheaf (smallEtaleTopology (ofOver ybar.overObj)) AddCommGrpCat.{u + 1})
              n).map
            (smallEtaleDerivedBaseChangeHom f ybar.hom
              (geometricFiberToPoint f ybar) (geometricFiberToX f ybar)
              (geometricFiber_isPullback f ybar) E)) ≫
        (derivedUniquePointHomologyIsoFibreCohomology f ybar
            (geometricFiberDerived f ybar E) n).hom :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
