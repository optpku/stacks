/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.SmallTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fppf.RingedComparison
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Square

/-! # The total fppf–étale square of ringed topoi -/

set_option backward.privateInPublic true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.SimplicialObject
open RingedSite RingedSite.ToposHom CategoryTheory.Sheaf.InternalRing
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open AlgebraicGeometry.AlgebraicSpace.Fppf
open scoped Simplicial MorphismOfTopoiIn

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} (U : SimplicialObject (AlgebraicSpace S))

/-- Total étale restriction commutes with forgetting the ring coefficients. -/
def toSliceTotal_forgetIso :
    (toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) ⋙
      sheafCompose (spacesEtaleTotalTopology U) (forget RingCat.{u}) ≅
    sheafCompose (sliceTotalTopology (fppfTopology S) U) (forget RingCat.{u}) ⋙
      (SmallCoefficients.fppfEtaleComparison U).pushforward :=
  eqToIso (Functor.sheafPushforwardContinuous.compSheafCompose (toSliceTotal U)
    (forget RingCat.{u}) (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))

/-- The total horizontal section comparison is identity on the common global-section ring. -/
private def totalComparisonSection (Y : (SpacesEtale U)ᵒᵖ) :
    (etaleTotalStructureSheaf U).obj.obj Y ⟶
      (((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)).obj
          (fppfTotalStructureSheaf U)).obj.obj Y :=
  (Functor.sheafPushforwardContinuousObjObjIso (toSliceTotal U)
    (J := spacesEtaleTotalTopology U) RingCat.{u} (fppfTotalStructureSheaf U) Y.unop).inv

/-- The common total section rings have compatible restriction maps. -/
theorem fppfEtaleRingedComparison_structureSheafMap_naturality
    {Y Z : (SpacesEtale U)ᵒᵖ} (f : Y ⟶ Z) :
    (etaleTotalStructureSheaf U).obj.map f ≫ totalComparisonSection U Z =
      totalComparisonSection U Y ≫
        (((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)).obj
            (fppfTotalStructureSheaf U)).obj.map f := sorry

/-- The direct structure map is identity on the common section rings in every degree. -/
def fppfEtaleRingedComparison_structureSheafMap :
    (etaleTotalRingedSite U).structureSheaf ⟶
      ((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U)).obj
          (fppfTotalRingedSite U).structureSheaf :=
  ObjectProperty.homMk
    { app := totalComparisonSection U
      naturality := fun _ _ f ↦ fppfEtaleRingedComparison_structureSheafMap_naturality U f }

/-- The canonical total section comparison preserves internal ring operations. -/
theorem fppfEtaleRingedComparison_isRingCompatible :
    @Direct.IsRingCompatible (fppfTotalRingedSite U) (etaleTotalRingedSite U) _ _
      (SmallCoefficients.fppfEtaleComparison U)
      ((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
      (toSliceTotal_forgetIso U) (fppfEtaleRingedComparison_structureSheafMap U) := sorry

/-- The canonical comparison from the total fppf ringed topos to the total étale ringed topos. -/
def fppfEtaleRingedComparison : ToposHom (fppfTotalRingedSite U) (etaleTotalRingedSite U) :=
  @ofDirectImage (fppfTotalRingedSite U) (etaleTotalRingedSite U) _ _
    (SmallCoefficients.fppfEtaleComparison U)
    ((toSliceTotal U).sheafPushforwardContinuous RingCat.{u}
      (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U))
    (toSliceTotal_forgetIso U) (fppfEtaleRingedComparison_structureSheafMap U)
    (fppfEtaleRingedComparison_isRingCompatible U)

/-- The underlying total comparison is the small-coefficient geometric morphism. -/
theorem fppfEtaleRingedComparison_toTopos :
    (fppfEtaleRingedComparison U).toTopos = SmallCoefficients.fppfEtaleComparison U := rfl

/-- The direct image of the total comparison is restriction along the total inclusion. -/
theorem fppfEtaleRingedComparison_pushforward :
    (fppfEtaleRingedComparison U).toTopos.pushforward =
      (toSliceTotal U).sheafPushforwardContinuous (Type u)
        (spacesEtaleTotalTopology U) (sliceTotalTopology (fppfTopology S) U) := rfl

/-- Compatibility of a direct-image map of underlying structure sheaves with their internal rings. -/
private abbrev UnderlyingRingCompatible
    (A B : RingedSite.{u+1,u+1,u})
    [A.siteTopology.HasSheafCompose (forget RingCat.{u})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{u})]
    (f : MorphismOfTopoiIn.{u+1,u+1,u+1,u+1,u} B.siteTopology A.siteTopology)
    (α : RingedSite.Hom.underlyingStructureSheaf B ⟶
      f.pushforward.obj (RingedSite.Hom.underlyingStructureSheaf A)) : Prop :=
  @IsRingHom (Sheaf B.siteTopology (Type u)) _ _
    (RingObjects.carrier B.siteTopology (toInternal.obj B.structureSheaf))
    (RingObjects.carrier B.siteTopology (f.internalRingDirectImage.obj (toInternal.obj A.structureSheaf)))
    (RingObjects.ringObj B.siteTopology (toInternal.obj B.structureSheaf)).toAddGrpObj.toAddMonObj
    (RingObjects.ringObj B.siteTopology
      (f.internalRingDirectImage.obj (toInternal.obj A.structureSheaf))).toAddGrpObj.toAddMonObj
    (RingObjects.ringObj B.siteTopology (toInternal.obj B.structureSheaf)).toMonObj
    (RingObjects.ringObj B.siteTopology
      (f.internalRingDirectImage.obj (toInternal.obj A.structureSheaf))).toMonObj α

/-- Taking the internal-ring adjoint of a compatible direct structure map gives a ringed-topos map. -/
private def ringedOfUnderlying
    (A B : RingedSite.{u+1,u+1,u})
    [A.siteTopology.HasSheafCompose (forget RingCat.{u})]
    [B.siteTopology.HasSheafCompose (forget RingCat.{u})]
    (f : MorphismOfTopoiIn.{u+1,u+1,u+1,u+1,u} B.siteTopology A.siteTopology)
    (α : RingedSite.Hom.underlyingStructureSheaf B ⟶
      f.pushforward.obj (RingedSite.Hom.underlyingStructureSheaf A))
    (h : UnderlyingRingCompatible A B f α) : ToposHom A B where
  toTopos := f
  structureMap := fromInternal.map ((f.internalRingAdjunction.homEquiv _ _).symm
    (@RingObjCat.Hom.mk (Sheaf B.siteTopology (Type u)) _ _ (sheafBraidedCategory B.siteTopology)
      (toInternal.obj B.structureSheaf)
      (f.internalRingDirectImage.obj (toInternal.obj A.structureSheaf)) α h)) ≫
    toFromIso.hom.app A.structureSheaf

variable {X : AlgebraicSpace S} (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)

/-- Projection of the degree-zero cartesian object to its object over the augmentation target. -/
private def augmentationPullbackFst (V : Over X) :
    pullback V.hom (a.app (op ⦋0⦌)) ⟶ V.left := pullback.fst _ _

/-- The degree-zero stage of augmentation direct image of the underlying fppf structure sheaf. -/
private def fppfStructureZero :=
  ((SmallCoefficients.fppfAugmentationStage U a ⦋0⦌).sheafPushforwardContinuous (Type u)
    (overFppfTopology X) (sliceTotalTopology (fppfTopology S) U)).obj
      (RingedSite.Hom.underlyingStructureSheaf (fppfTotalRingedSite U))

/-- A section is pulled back along the cartesian projection in degree zero. -/
private def fppfStructureZeroApp (V : (Over X)ᵒᵖ) :
    (RingedSite.Hom.underlyingStructureSheaf (overFppfRingedSite X)).obj.obj V ⟶
      (fppfStructureZero U a).obj.obj V :=
  (↾fun x ↦ ((forget₂ CommRingCat RingCat).map
    (Etale.Atlas.globalSectionsRingMap (augmentationPullbackFst U a V.unop))) x) ≫
  (Functor.sheafPushforwardContinuousObjObjIso (SmallCoefficients.fppfAugmentationStage U a ⦋0⦌)
    (J := overFppfTopology X) (Type u)
    (RingedSite.Hom.underlyingStructureSheaf (fppfTotalRingedSite U)) V.unop).inv

/-- The two restrictions of a pulled-back global section to degree one coincide. -/
theorem fppfAugmentationRinged_structureSheafMap_equalizes (V : (Over X)ᵒᵖ) :
    fppfStructureZeroApp U a V ≫
      (SmallCoefficients.fppfAugmentationParallel U a (Type u)
        (RingedSite.Hom.underlyingStructureSheaf (fppfTotalRingedSite U)) 0).hom.app V =
    fppfStructureZeroApp U a V ≫
      (SmallCoefficients.fppfAugmentationParallel U a (Type u)
        (RingedSite.Hom.underlyingStructureSheaf (fppfTotalRingedSite U)) 1).hom.app V := sorry

/-- Cartesian projection on global sections is natural in the object over the target. -/
theorem fppfAugmentationRinged_structureSheafMap_naturality
    {V W : (Over X)ᵒᵖ} (f : V ⟶ W) :
    (RingedSite.Hom.underlyingStructureSheaf (overFppfRingedSite X)).obj.map f ≫
      fppfStructureZeroApp U a W =
    fppfStructureZeroApp U a V ≫ (fppfStructureZero U a).obj.map f := sorry

/-- The degree-zero cartesian pullback on sections. -/
private def fppfStructureZeroMap :
    RingedSite.Hom.underlyingStructureSheaf (overFppfRingedSite X) ⟶ fppfStructureZero U a :=
  ObjectProperty.homMk
    { app := fppfStructureZeroApp U a
      naturality := fun _ _ f ↦ fppfAugmentationRinged_structureSheafMap_naturality U a f }

/-- Pullback of global sections along all augmentation stages, factored through the coface equalizer. -/
def fppfAugmentationRinged_structureSheafMap :
    RingedSite.Hom.underlyingStructureSheaf (overFppfRingedSite X) ⟶
      (SmallCoefficients.fppfAugmentation U a).pushforward.obj
        (RingedSite.Hom.underlyingStructureSheaf (fppfTotalRingedSite U)) :=
  equalizer.lift (fppfStructureZeroMap U a) (by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    exact fppfAugmentationRinged_structureSheafMap_equalizes U a V)

/-- Cartesian pullback on sections is a homomorphism of the canonical internal rings. -/
theorem fppfAugmentationRinged_isRingCompatible :
    UnderlyingRingCompatible (fppfTotalRingedSite U) (overFppfRingedSite X)
      (SmallCoefficients.fppfAugmentation U a) (fppfAugmentationRinged_structureSheafMap U a) := sorry

/-- The total fppf augmentation as a morphism of ringed topoi. -/
def fppfAugmentationRinged : ToposHom (fppfTotalRingedSite U) (overFppfRingedSite X) :=
  ringedOfUnderlying _ _ (SmallCoefficients.fppfAugmentation U a)
    (fppfAugmentationRinged_structureSheafMap U a) (fppfAugmentationRinged_isRingCompatible U a)

/-- The underlying fppf augmentation is the genuine all-stage geometric morphism. -/
theorem fppfAugmentationRinged_toTopos :
    (fppfAugmentationRinged U a).toTopos = SmallCoefficients.fppfAugmentation U a := rfl

/-- The cartesian pullback in degree zero has the expected underlying algebraic space. -/
private theorem augmentationFunctor_obj_left (V : spacesEtaleSite X) :
    ((augmentationFunctor U a).obj V).obj.left = pullback V.hom (a.app (op ⦋0⦌)) := rfl

/-- The canonical ring map from an étale object's structure sections to its degree-zero cartesian pullback. -/
private def augmentationDegreeZeroSection (V : (spacesEtaleSite X)ᵒᵖ) :
    (spacesStructureSheaf X).obj.obj V ⟶
      (((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).obj
          (etaleTotalStructureSheaf U)).obj.obj V :=
  Etale.Big.spacesStructureToGamma V.unop ≫
    (Etale.Big.gammaGlobalSectionsIso V.unop.left).hom ≫
    (forget₂ CommRingCat RingCat).map
      (Etale.Atlas.globalSectionsRingMap
        (augmentationPullbackFst U a ((spacesEtaleToBig X).obj V.unop))) ≫
    (Functor.sheafPushforwardContinuousObjObjIso (augmentationFunctor U a)
      (J := spacesEtaleTopology X) RingCat.{u} (etaleTotalStructureSheaf U) V.unop).inv

/-- The degree-zero section pullbacks commute with étale restriction maps. -/
theorem augmentationDegreeZeroStructureSheafMap_naturality
    {V W : (spacesEtaleSite X)ᵒᵖ} (f : V ⟶ W) :
    (spacesStructureSheaf X).obj.map f ≫ augmentationDegreeZeroSection U a W =
      augmentationDegreeZeroSection U a V ≫
        (((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
          (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).obj
            (etaleTotalStructureSheaf U)).obj.map f := sorry

/-- The ring-valued section map associated to the degree-zero cartesian pullback functor. -/
def spacesEtaleAugmentationRinged_structureSheafMap :
    (spacesRingedSite X).structureSheaf ⟶
      ((augmentationFunctor U a).sheafPushforwardContinuous RingCat.{u}
        (spacesEtaleTopology X) (spacesEtaleTotalTopology U)).obj
          (etaleTotalRingedSite U).structureSheaf :=
  ObjectProperty.homMk
    { app := augmentationDegreeZeroSection U a
      naturality := fun _ _ f ↦ augmentationDegreeZeroStructureSheafMap_naturality U a f }

/-- The degree-zero direct image of the total étale structure sheaf along the augmentation. -/
private def etaleStructureZero :=
  (spacesRingedMorphismOfTopoi (a.app (op ⦋0⦌))).pushforward.obj
    ((SmallCoefficients.spacesEtaleRestrict U ⦋0⦌).obj
      (RingedSite.Hom.underlyingStructureSheaf (etaleTotalRingedSite U)))

/-- The canonical degree-zero section map, with type coefficients. -/
private def etaleStructureZeroApp (V : (spacesEtaleSite X)ᵒᵖ) :
    (RingedSite.Hom.underlyingStructureSheaf (spacesRingedSite X)).obj.obj V ⟶
      (etaleStructureZero U a).obj.obj V :=
  ↾fun x ↦ (augmentationDegreeZeroSection U a V) x

/-- The canonical section map satisfies the two-coface descent condition. -/
theorem spacesEtaleAugmentationRinged_totalStructureSheafMap_equalizes
    (V : (spacesEtaleSite X)ᵒᵖ) :
    etaleStructureZeroApp U a V ≫
      (SmallCoefficients.spacesEtaleAugmentationParallel U a
        (RingedSite.Hom.underlyingStructureSheaf (etaleTotalRingedSite U)) 0).hom.app V =
    etaleStructureZeroApp U a V ≫
      (SmallCoefficients.spacesEtaleAugmentationParallel U a
        (RingedSite.Hom.underlyingStructureSheaf (etaleTotalRingedSite U)) 1).hom.app V := sorry

/-- The canonical degree-zero section map is natural as a map to stage direct image. -/
theorem spacesEtaleAugmentationRinged_totalStructureSheafMap_naturality
    {V W : (spacesEtaleSite X)ᵒᵖ} (f : V ⟶ W) :
    (RingedSite.Hom.underlyingStructureSheaf (spacesRingedSite X)).obj.map f ≫
      etaleStructureZeroApp U a W =
    etaleStructureZeroApp U a V ≫ (etaleStructureZero U a).obj.map f := sorry

/-- The degree-zero section map into the stage direct image. -/
private def etaleStructureZeroMap :
    RingedSite.Hom.underlyingStructureSheaf (spacesRingedSite X) ⟶ etaleStructureZero U a :=
  ObjectProperty.homMk
    { app := etaleStructureZeroApp U a
      naturality := fun _ _ f ↦ spacesEtaleAugmentationRinged_totalStructureSheafMap_naturality U a f }

/-- The total étale augmentation structure map is the canonical section pullback in the coface equalizer. -/
def spacesEtaleAugmentationRinged_totalStructureSheafMap :
    RingedSite.Hom.underlyingStructureSheaf (spacesRingedSite X) ⟶
      (SmallCoefficients.spacesEtaleAugmentation U a).pushforward.obj
        (RingedSite.Hom.underlyingStructureSheaf (etaleTotalRingedSite U)) :=
  equalizer.lift (etaleStructureZeroMap U a)
    (by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext V
      exact spacesEtaleAugmentationRinged_totalStructureSheafMap_equalizes U a V)

/-- The total étale section pullback preserves the canonical internal ring operations. -/
theorem spacesEtaleAugmentationRinged_isRingCompatible :
    UnderlyingRingCompatible (etaleTotalRingedSite U) (spacesRingedSite X)
      (SmallCoefficients.spacesEtaleAugmentation U a)
      (spacesEtaleAugmentationRinged_totalStructureSheafMap U a) := sorry

/-- The genuine total étale augmentation, with its canonical structure-sheaf map. -/
def spacesEtaleAugmentationRinged : ToposHom (etaleTotalRingedSite U) (spacesRingedSite X) :=
  ringedOfUnderlying _ _ (SmallCoefficients.spacesEtaleAugmentation U a)
    (spacesEtaleAugmentationRinged_totalStructureSheafMap U a)
    (spacesEtaleAugmentationRinged_isRingCompatible U a)

/-- The underlying étale augmentation has the canonical inverse image in every degree. -/
theorem spacesEtaleAugmentationRinged_toTopos :
    (spacesEtaleAugmentationRinged U a).toTopos = SmallCoefficients.spacesEtaleAugmentation U a := rfl

/-- The degree-zero component of the total structure map is the cartesian pullback of sections. -/
theorem spacesEtaleAugmentationRinged_structureMap_restrict :
    spacesEtaleAugmentationRinged_totalStructureSheafMap U a ≫
      equalizer.ι
        (SmallCoefficients.spacesEtaleAugmentationParallel U a
          (RingedSite.Hom.underlyingStructureSheaf (etaleTotalRingedSite U)) 0)
        (SmallCoefficients.spacesEtaleAugmentationParallel U a
          (RingedSite.Hom.underlyingStructureSheaf (etaleTotalRingedSite U)) 1) =
      etaleStructureZeroMap U a := sorry

/-- The underlying comparison of direct images around the canonical ringed square. -/
def fppfEtaleRingedCommSq_homIso :
    (ToposHom.comp (fppfEtaleRingedComparison U) (spacesEtaleAugmentationRinged U a)).toTopos.pushforward ≅
      (ToposHom.comp (fppfAugmentationRinged U a) (Fppf.spacesRingedComparison X)).toTopos.pushforward :=
  SmallCoefficients.fppfEtaleDirectImageSquare U a

/-- The canonical direct-image comparison respects the two composite structure-sheaf maps. -/
theorem fppfEtaleRingedCommSq_comm :
    (ToposHom.comp (fppfEtaleRingedComparison U) (spacesEtaleAugmentationRinged U a)).directStructureMap ≫
      (MorphismOfTopoiIn.ringDirectImageNatTrans (fppfEtaleRingedCommSq_homIso U a).hom).app
        (fppfTotalRingedSite U).structureSheaf =
      (ToposHom.comp (fppfAugmentationRinged U a) (Fppf.spacesRingedComparison X)).directStructureMap := sorry

/-- The canonical total fppf and étale augmentations form a commutative square of ringed topoi. -/
def fppfEtaleRingedCommSq :
    ToposHom.CommSquare (fppfTotalRingedSite U) (etaleTotalRingedSite U)
      (overFppfRingedSite X) (spacesRingedSite X) where
  upper := fppfEtaleRingedComparison U
  left := fppfAugmentationRinged U a
  right := spacesEtaleAugmentationRinged U a
  lower := Fppf.spacesRingedComparison X
  cell := { homIso := fppfEtaleRingedCommSq_homIso U a
            comm := fppfEtaleRingedCommSq_comm U a }

/-- The upper edge is the canonical total comparison. -/
theorem fppfEtaleRingedCommSq_upper :
    (fppfEtaleRingedCommSq U a).upper = fppfEtaleRingedComparison U := rfl

/-- The left edge is the genuine total fppf augmentation. -/
theorem fppfEtaleRingedCommSq_left :
    (fppfEtaleRingedCommSq U a).left = fppfAugmentationRinged U a := rfl

/-- The right edge is the genuine total étale augmentation. -/
theorem fppfEtaleRingedCommSq_right :
    (fppfEtaleRingedCommSq U a).right = spacesEtaleAugmentationRinged U a := rfl

/-- The lower edge is the canonical comparison over the target of the augmentation. -/
theorem fppfEtaleRingedCommSq_lower :
    (fppfEtaleRingedCommSq U a).lower = Fppf.spacesRingedComparison X := rfl

/-- In every degree the total inclusion is the canonical inclusion of the spaces-étale site. -/
theorem toSliceTotal_comp_includeStage (n : SimplexCategoryᵒᵖ) :
    SpacesEtale.includeStage (U := U) n ⋙ toSliceTotal U =
      spacesEtaleToBig (U.obj n) ⋙ Grothendieck.ι (sliceDiagram U) n := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
