/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.NaiveCotangent.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Pullback.Ext
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.CotangentComplex.NaiveComparison

@[expose] public section
open CategoryTheory CategoryTheory.Limits
open scoped DerivedExt RingedSite.ToposHom
noncomputable section
universe u
namespace RingedSite.ToposHom.NaiveCotangent

-- Local instance justification (defeq pin): the naive cotangent Ext maps use the standard module derived category of the extension classification.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the unbundled cotangent complex uses the same standard localization as modules on its ringed site.
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

/-- The structure map of a composite is compatible with successive inverse image. -/
theorem compStructureSquare :
    CommSq (MorphismOfTopoiIn.commRingInverseImageCompIso f.toTopos g.toTopos OB).inv
      (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
      (commRingStructureMap (g.comp f)) (Thickening.normalizedProjection g) := sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The derived cotangent comparison is the counit followed by inverse-image and composition maps. -/
def comparison :
    (DerivedPullback.functor g).obj ((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f]) ⟶
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj NL[g.comp f] :=
  (DerivedPullback.counit g).app NL[f] ≫
    DerivedCategory.Q.map
      (underivedComparison
        (hcolC := @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ JC CommRingCat.{u} _
          (Discrete WalkingPair) _ inferInstance (by infer_instance))
        (hcolD := @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ JD CommRingCat.{u} _
          (Discrete WalkingPair) _ inferInstance (by infer_instance)) g (commRingStructureMap f) ≫
        SheafOfModules.RingedSite.NaiveCotangent.map (compStructureSquare f g))

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The derived cotangent comparison is computed by its three canonical constituent maps. -/
theorem comparison_spec :
    comparison f g =
      (DerivedPullback.counit g).app NL[f] ≫
        DerivedCategory.Q.map
          (underivedComparison
        (hcolC := @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ JC CommRingCat.{u} _
          (Discrete WalkingPair) _ inferInstance (by infer_instance))
        (hcolD := @CategoryTheory.Sheaf.instHasColimitsOfShape _ _ JD CommRingCat.{u} _
          (Discrete WalkingPair) _ inferInstance (by infer_instance)) g (commRingStructureMap f) ≫
            SheafOfModules.RingedSite.NaiveCotangent.map (compStructureSquare f g)) := sorry

variable {F : ModuleCat.{u} (ofCommRingSheaf JC OC)}
variable {G : ModuleCat.{u} (ofCommRingSheaf JD OD)}

/-- The derived coefficient map is augmentation, the single-complex comparison, and the given map. -/
def coeffDerived (c : g.modulePullback.obj F ⟶ G) :
    (DerivedPullback.functor g).obj
      ((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj ((CochainComplex.singleFunctor _ 0).obj F)) ⟶
        (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj ((CochainComplex.singleFunctor _ 0).obj G) :=
  (DerivedPullback.counit g).app ((CochainComplex.singleFunctor (ModuleCat.{u} (ofCommRingSheaf JC OC)) 0).obj F) ≫
    DerivedCategory.Q.map
      ((@HomologicalComplex.singleMapHomologicalComplex _ _ _ _ _ _ _ _ _
        g.modulePullback
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
          g.modulePullback (modulePullback_additive g)) (ComplexShape.up ℤ) inferInstance (0 : ℤ)).hom.app F ≫
          (CochainComplex.singleFunctor _ 0).map c)

/-- The coefficient comparison uses the counit and the canonical single-complex comparison. -/
theorem coeffDerived_spec (c : g.modulePullback.obj F ⟶ G) :
    coeffDerived g c =
      (DerivedPullback.counit g).app ((CochainComplex.singleFunctor (ModuleCat.{u} (ofCommRingSheaf JC OC)) 0).obj F) ≫
        DerivedCategory.Q.map
          ((@HomologicalComplex.singleMapHomologicalComplex _ _ _ _ _ _ _ _ _
            g.modulePullback
            (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _
              g.modulePullback (modulePullback_additive g)) (ComplexShape.up ℤ) inferInstance (0 : ℤ)).hom.app F ≫
              (CochainComplex.singleFunctor _ 0).map c) := sorry

/-- Pullback and coefficient postcomposition transport a relative extension class. -/
def extOneMap (c : g.modulePullback.obj F ⟶ G)
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    Ext⁽(1 : ℤ)⁾((DerivedPullback.functor g).obj ((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f]),
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  DerivedPullback.mapExt g ξ ≫ (shiftFunctor _ (1 : ℤ)).map (coeffDerived g c)

/-- Precomposition by the cotangent comparison transports a relative extension class. -/
def extOneComap
    (ζ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj NL[g.comp f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Ext⁽(1 : ℤ)⁾((DerivedPullback.functor g).obj ((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f]),
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj ((CochainComplex.singleFunctor _ 0).obj G)) :=
  comparison f g ≫ ζ

/-- Covariant Ext transport is derived pullback followed by shifted coefficient postcomposition. -/
theorem extOneMap_spec (c : g.modulePullback.obj F ⟶ G)
    (ξ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj ((CochainComplex.singleFunctor _ 0).obj F))) :
    extOneMap f g c ξ =
      DerivedPullback.mapExt g ξ ≫ (shiftFunctor _ (1 : ℤ)).map (coeffDerived g c) := sorry

/-- Contravariant Ext transport is precomposition by the cotangent comparison. -/
theorem extOneComap_spec
    (ζ : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj NL[g.comp f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    extOneComap f g ζ = comparison f g ≫ ζ := sorry

/-- Covariant transport preserves the zero extension class. -/
theorem extOneMap_zero (c : g.modulePullback.obj F ⟶ G) :
    extOneMap f g c (0 : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj NL[f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JC OC))).obj ((CochainComplex.singleFunctor _ 0).obj F))) = 0 := sorry

/-- Contravariant transport preserves the zero extension class. -/
theorem extOneComap_zero :
    extOneComap f g (0 : Ext⁽(1 : ℤ)⁾((DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj NL[g.comp f],
      (DerivedCategory.Q (C := ModuleCat.{u} (ofCommRingSheaf JD OD))).obj ((CochainComplex.singleFunctor _ 0).obj G))) = 0 := sorry

end RingedSite.ToposHom.NaiveCotangent
