/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings.Ext
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Equivalence
public import ReasLib.Algebra.Category.CommRingCat.Colimits

/-! # Ext comparison for geometric inverse image and derived scalar extension -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open scoped DerivedExt RingedSite.ToposHom

noncomputable section
set_option backward.privateInPublic true
set_option maxHeartbeats 4000000
set_option maxRecDepth 2500
set_option synthInstance.maxHeartbeats 100000

universe u
namespace RingedSite.ToposHom.AlgebraExtension

-- Local instance justification (defeq pin): the cell-derived pullback and same-site total derived extension must share the standard module derived category.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the unbundled commutative module category must select the same standard localization dictionary.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {B : Type u} [Category.{u} B] {JB : GrothendieckTopology B}
variable [JB.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JB.HasSheafCompose (forget RingCat.{u})]
variable [JB.HasSheafCompose (forget CommRingCat.{u})]
variable [JB.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JB CommRingCat.{u}] [JB.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JB AddCommGrpCat.{u}] [JB.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OB : Sheaf JB CommRingCat.{u}}
variable {C : Type u} [Category.{u} C] {JC : GrothendieckTopology C}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JC.HasSheafCompose (forget RingCat.{u})]
variable [JC.HasSheafCompose (forget CommRingCat.{u})]
variable [JC.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JC CommRingCat.{u}] [JC.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JC AddCommGrpCat.{u}] [JC.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OC : Sheaf JC CommRingCat.{u}}
variable {D : Type u} [Category.{u} D] {JD : GrothendieckTopology D}
variable [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [JD.HasSheafCompose (forget RingCat.{u})]
variable [JD.HasSheafCompose (forget CommRingCat.{u})]
variable [JD.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify JD CommRingCat.{u}] [JD.WEqualsLocallyBijective CommRingCat.{u}]
variable [HasSheafify JD AddCommGrpCat.{u}] [JD.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {OD : Sheaf JD CommRingCat.{u}}
variable (f : ToposHom (ofCommRingSheaf JC OC) (ofCommRingSheaf JB OB))
variable (g : ToposHom (ofCommRingSheaf JD OD) (ofCommRingSheaf JC OC))
variable [(SheafOfModules.restrictScalars.{u} g.structureMap).IsRightAdjoint]

variable {F : ModuleCat.{u} (ofCommRingSheaf JC OC)}
variable {G : ModuleCat.{u} (ofCommRingSheaf JD OD)}

/-- Geometric inverse image transported to modules over the commutative inverse-image ring. -/
private def geometricModules :
    ModuleCat.{u} (ofCommRingSheaf JC OC) ⥤
      SheafOfModules (ringSheaf JD (g.toTopos.commRingInverseImage.obj OC)) :=
  g.toTopos.moduleInverseImage (ringSheaf JC OC) ⋙
    SheafOfModules.restrictScalars (g.toTopos.commRingInverseImageForgetRingIso.hom.app OC)

/-- Additivity of transported geometric inverse image. -/
private abbrev geometricAdditive : (geometricModules g).Additive where
  map_add := fun {X Y a b} ↦
    (congrArg
      (SheafOfModules.restrictScalars
        (g.toTopos.commRingInverseImageForgetRingIso.hom.app OC)).map
      (@Functor.Additive.map_add _ _ _ _ _ _ _
        (g.toTopos.moduleInverseImage_additive (ringSheaf JC OC)) X Y a b)).trans
      (Functor.map_add _)

/-- Transported geometric inverse image applied degreewise to complexes. -/
private def geometricComplex :
    CochainComplex (ModuleCat.{u} (ofCommRingSheaf JC OC)) ℤ ⥤
      CochainComplex (SheafOfModules
        (ringSheaf JD (g.toTopos.commRingInverseImage.obj OC))) ℤ :=
  @Functor.mapHomologicalComplex _ _ _ _ _ _ _ (geometricModules g)
    (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (geometricAdditive g))
    (ComplexShape.up ℤ)

/-- The ringed-topos morphism with unchanged inverse-image structure ring. -/
private def geometricHom :
    ToposHom (ofCommRingSheaf JD (g.toTopos.commRingInverseImage.obj OC))
      (ofCommRingSheaf JC OC) where
  toTopos := g.toTopos
  structureMap := g.toTopos.commRingInverseImageForgetRingIso.inv.app OC

/-- Scalar extension along the inverse ring comparison is restriction along its inverse. -/
private def geometricScalarIso :
    (geometricHom g).modulePullback ≅ geometricModules g :=
  Functor.isoWhiskerLeft (g.toTopos.moduleInverseImage (ringSheaf JC OC))
    (Adjunction.leftAdjointUniq (ModulePullback.scalarAdjunction (geometricHom g))
      (SheafOfModules.ChangeOfRings.restrictScalarsEquivalence
        (g.toTopos.commRingInverseImageForgetRingIso.app OC)).symm.toAdjunction)

/-- Scalar extension along the normalized geometric identity ring map is the identity. -/
private def geometricIdentityIso :
    extendComplex (Thickening.normalizedProjection (geometricHom g)) ≅ 𝟭 _ :=
  eqToIso (congrArg extendComplex
    ((congrArg
      (CategoryTheory.Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimage)
      (g.toTopos.commRingInverseImageForgetRingIso.app OC).hom_inv_id).trans
        CategoryTheory.Sheaf.InternalCommRing.CommRingSheaves.fullyFaithfulForgetRing.preimage_id)) ≪≫
    extendComplexIdIso _

/-- The cotangent comparison induced by geometric inverse image of the canonical free presentation. -/
private def cotangentInverseImageComparison :
    DerivedCategory.Q.obj ((geometricComplex g).obj NL[f]) ⟶
      DerivedCategory.Q.obj
        (SheafOfModules.RingedSite.NaiveCotangent.obj
          (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB))
          (Under.mk (g.toTopos.commRingInverseImage.map (commRingStructureMap f)))) :=
  DerivedCategory.Q.map
    ((@NatIso.mapHomologicalComplex _ _ _ _ _ _ _ _ _
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _
        (modulePullback_additive (geometricHom g)))
      (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (geometricAdditive g))
      (geometricScalarIso g) (ComplexShape.up ℤ)).inv.app NL[f] ≫
      NaiveCotangent.underivedComparison
        (hcolC := @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ JC CommRingCat.{u} _
          (Discrete WalkingPair) _ inferInstance inferInstance)
        (hcolD := @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ JD CommRingCat.{u} _
          (Discrete WalkingPair) _ inferInstance inferInstance)
        (geometricHom g) (commRingStructureMap f) ≫
      (geometricIdentityIso g).hom.app _)

/-- Geometric inverse image commutes with the relative naive cotangent complex. -/
private theorem cotangentInverseImageComparison_isIso :
    IsIso (cotangentInverseImageComparison f g) := sorry

/-- The relative naive cotangent complex of the inverse-image algebra is its geometric inverse image. -/
def cotangentInverseImageIso :
    DerivedCategory.Q.obj
      (SheafOfModules.RingedSite.NaiveCotangent.obj
        (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB))
        (Under.mk (g.toTopos.commRingInverseImage.map (commRingStructureMap f)))) ≅
      DerivedCategory.Q.obj ((geometricComplex g).obj NL[f]) :=
  (@asIso _ _ _ _ (cotangentInverseImageComparison f g)
    (cotangentInverseImageComparison_isIso f g)).symm

/-- The inverse ring comparison followed by the commutative structure map is the original structure map. -/
private abbrev scalarFactorEquality :
    g.structureMap = g.toTopos.commRingInverseImageForgetRingIso.inv.app OC ≫
      ringSheafMap (commRingStructureMap g) :=
  ((congrArg (fun k ↦ g.toTopos.commRingInverseImageForgetRingIso.inv.app OC ≫ k)
    (commRingStructureMap_forget g)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ g.structureMap)
          (g.toTopos.commRingInverseImageForgetRingIso.app OC).inv_hom_id).trans
            (Category.id_comp _)))).symm

/-- The scalar factorization of module pullback through the commutative inverse-image ring. -/
private def scalarFactorIso :
    SheafOfModules.restrictScalars
        (g.toTopos.commRingInverseImageForgetRingIso.hom.app OC) ⋙
      extendAlong (commRingStructureMap g) ≅
    SheafOfModules.ChangeOfRings.extendScalars g.structureMap :=
  Adjunction.leftAdjointUniq
    (((SheafOfModules.ChangeOfRings.restrictScalarsEquivalence
        (g.toTopos.commRingInverseImageForgetRingIso.app OC)).symm.toAdjunction.comp
      (extendRestrictAdj (commRingStructureMap g))).ofNatIsoRight
        (SheafOfModules.Restriction.compIso'
          (g.toTopos.commRingInverseImageForgetRingIso.inv.app OC)
          (ringSheafMap (commRingStructureMap g)) g.structureMap (scalarFactorEquality g)))
    (ModulePullback.scalarAdjunction g)

/-- Module pullback factors as geometric inverse image followed by scalar extension. -/
private def moduleFactorIso :
    g.modulePullback ≅ geometricModules g ⋙ extendAlong (commRingStructureMap g) :=
  Functor.isoWhiskerLeft (g.toTopos.moduleInverseImage (ringSheaf JC OC))
      (scalarFactorIso g).symm ≪≫ (Functor.associator _ _ _).symm

/-- Geometric inverse image takes the canonical cell augmentation to an isomorphism after localization. -/
private theorem derivedPullbackFactor_laws :
    IsIso (DerivedCategory.Q.map ((geometricComplex g).map
      (SheafOfModules.CellReplacement.augmentation NL[f]))) := sorry

/-- The canonical comparison from scalar-derived geometric inverse image to derived pullback. -/
private def derivedPullbackFactorComparison :
    (SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap g)).obj
      (DerivedCategory.Q.obj ((geometricComplex g).obj NL[f])) ⟶
    (DerivedPullback.functor g).obj (DerivedCategory.Q.obj NL[f]) :=
  (SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap g)).map
    (@asIso _ _ _ _
      (DerivedCategory.Q.map ((geometricComplex g).map
        (SheafOfModules.CellReplacement.augmentation NL[f])))
      (derivedPullbackFactor_laws f g)).inv ≫
    (@Functor.LeftDerived.Homotopy.cochainCounit _ _ _ _ _ _ _ _
      ((sameSiteHom (commRingStructureMap g)).modulePullback) inferInstance
      (RingedSite.Hom.modulePullback.DerivedCategory.hasLeftDerived
        (sameSiteHom (commRingStructureMap g)))).app
      ((geometricComplex g).obj (SheafOfModules.CellReplacement.model NL[f])) ≫
    DerivedCategory.Q.map
      ((pullbackComplexExtendIso (commRingStructureMap g)).hom.app _ ≫
        (@Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
          (moduleFactorIso g).symm (geometricAdditive g) inferInstance
          (modulePullback_additive g) (ComplexShape.up ℤ)).hom.app
          (SheafOfModules.CellReplacement.model NL[f])) ≫
    (@Functor.CellModel.fac _ _ _ _ _ _ _ _ _ _ _ g.modulePullback
      (modulePullback_additive g) (DerivedPullback.invertsQuasiIso g)).inv.app NL[f]

/-- Geometric exactness identifies scalar-derived geometric inverse image with derived pullback. -/
private theorem derivedPullbackFactorComparison_isIso :
    IsIso (derivedPullbackFactorComparison f g) := sorry

/-- Derived pullback of the relative cotangent complex factors through geometric inverse image
and derived extension along the canonical commutative structure map. -/
def derivedPullbackFactorIso :
    (DerivedPullback.functor g).obj (DerivedCategory.Q.obj NL[f]) ≅
    (SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap g)).obj
      (DerivedCategory.Q.obj
        (SheafOfModules.RingedSite.NaiveCotangent.obj
          (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB))
          (Under.mk (g.toTopos.commRingInverseImage.map (commRingStructureMap f))))) :=
  (@asIso _ _ _ _ (derivedPullbackFactorComparison f g)
    (derivedPullbackFactorComparison_isIso f g)).symm ≪≫
      (SheafOfModules.RingedSite.SameSite.pullbackDerived (commRingStructureMap g)).mapIso
        (cotangentInverseImageIso f g).symm

/-- Tensor–Hom adjunction identifies inverse-image relative Ext with Ext from derived pullback. -/
def extOneRestrictEquiv (G : ModuleCat.{u} (ofCommRingSheaf JD OD)) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
      (SheafOfModules.RingedSite.NaiveCotangent.obj
        (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB))
        (Under.mk (g.toTopos.commRingInverseImage.map (commRingStructureMap f)))),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((restrictionAlong (commRingStructureMap g)).obj G))) ≃
    Ext⁽(1 : ℤ)⁾((DerivedPullback.functor g).obj (DerivedCategory.Q.obj NL[f]),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  (SheafOfModules.RingedSite.SameSite.extRestrictEquiv (commRingStructureMap g) _ G (1 : ℤ)).trans
    { toFun := fun ξ ↦ (derivedPullbackFactorIso f g).hom ≫ ξ
      invFun := fun ξ ↦ (derivedPullbackFactorIso f g).inv ≫ ξ
      left_inv := fun ξ ↦ (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ ξ) (derivedPullbackFactorIso f g).inv_hom_id).trans
          (Category.id_comp _))
      right_inv := fun ξ ↦ (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k ↦ k ≫ ξ) (derivedPullbackFactorIso f g).hom_inv_id).trans
          (Category.id_comp _)) }

/-- The Ext identification is derived scalar counit transport followed by the factor comparison. -/
theorem extOneRestrictEquiv_apply (G : ModuleCat.{u} (ofCommRingSheaf JD OD))
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
      (SheafOfModules.RingedSite.NaiveCotangent.obj
        (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB))
        (Under.mk (g.toTopos.commRingInverseImage.map (commRingStructureMap f)))),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
        ((restrictionAlong (commRingStructureMap g)).obj G)))) :
    extOneRestrictEquiv f g G ξ = (derivedPullbackFactorIso f g).hom ≫
      SheafOfModules.RingedSite.SameSite.extRestrict (commRingStructureMap g) _ G (1 : ℤ) ξ := sorry

end RingedSite.ToposHom.AlgebraExtension
