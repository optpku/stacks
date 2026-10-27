/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension.InverseImage
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension.Ext
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension.Pushout
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.AlgebraExtension.Pullback

/-! # Functoriality of square-zero algebra extensions on ringed topoi -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.FirstOrderThickening
open SheafOfModules.RingedSite.FirstOrderThickening.Solution
open scoped DerivedExt RingedSite.ToposHom

noncomputable section
set_option maxHeartbeats 1600000

universe u
namespace RingedSite.ToposHom.AlgebraExtension

-- Local instance justification (defeq pin): extension classes and both derived transports must use the standard module derived category.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf module spelling must select the same standard localization dictionary.
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

/-- The scalar adjunct transported to modules over the commutative inverse-image ring. -/
def coefficientAdjunct (c : g.modulePullback.obj F ⟶ G) :
    inverseImageCoeff g F ⟶ (restrictionAlong (commRingStructureMap g)).obj G :=
  (SheafOfModules.restrictScalars
      (g.toTopos.commRingInverseImageForgetRingIso.hom.app OC)).map
        (ModulePullback.scalarHomEquiv g _ _ c) ≫
    (SheafOfModules.Restriction.compIso'
      (g.toTopos.commRingInverseImageForgetRingIso.hom.app OC) g.structureMap
      (ringSheafMap (commRingStructureMap g)) (commRingStructureMap_forget g)).hom.app G

/-- The transported scalar adjunct has the same underlying geometric coefficient carrier map. -/
theorem coefficientAdjunct_spec (c : g.modulePullback.obj F ⟶ G) :
    (g.toTopos.moduleInverseImageForgetIso (ringSheaf JC OC)).inv.app F ≫
      (ToInternal.underlying (ringSheaf JD (g.toTopos.commRingInverseImage.obj OC))).map
        (X := inverseImageCoeff g F)
        (Y := (restrictionAlong (commRingStructureMap g)).obj G)
        (coefficientAdjunct g c) = coefficientCarrierMap g c := sorry

/-- The inverse-image source extension pushed out along the transported coefficient adjunct. -/
def pushoutAlong (c : g.modulePullback.obj F ⟶ G) (S : AlgebraExtension f F) :
    Solution (𝟙 (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB)))
      (isSquareZero_id _) (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
      ((restrictionAlong (commRingStructureMap g)).obj G)
      (zeroKernelMap _ ((restrictionAlong (commRingStructureMap g)).obj G)) :=
  Solution.pushoutAlong (coefficientAdjunct g c) (inverseImage f g S)

/-- The target extension pulled back to the geometric inverse image of the source ring. -/
def pullbackAlong (S : AlgebraExtension (g.comp f) G) :
    Solution (𝟙 (g.toTopos.commRingInverseImage.obj (f.toTopos.commRingInverseImage.obj OB)))
      (isSquareZero_id _) (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
      ((restrictionAlong (commRingStructureMap g)).obj G)
      (zeroKernelMap _ ((restrictionAlong (commRingStructureMap g)).obj G)) :=
  Solution.pullbackAlong (normalizeComposite f g S)

/-- Geometric coefficient pushout respects quotient, inverse-image base, and coefficient kernels. -/
theorem pushoutAlong_spec (c : g.modulePullback.obj F ⟶ G) (S : AlgebraExtension f F) :
    Solution.Pushout.fromMiddle (coefficientAdjunct g c) (inverseImage f g S) ≫
        (pushoutAlong f g c S).proj = g.toTopos.commRingInverseImage.map S.proj ∧
    g.toTopos.commRingInverseImage.map S.structureMap ≫
        Solution.Pushout.fromMiddle (coefficientAdjunct g c) (inverseImage f g S) =
      (pushoutAlong f g c S).structureMap ∧
    (∀ U x,
      (Solution.Pushout.fromMiddle (coefficientAdjunct g c) (inverseImage f g S)).hom.app U
        ((g.toTopos.commRingInverseImageForgetIso.inv.app S.middle).hom.app U
          ((g.toTopos.inverseImage.map (kernelCarrierι f S)).hom.app U x)) =
      KernelIdeal.ιApp (pushoutAlong f g c S).proj U
        ((kernelIso_forget (pushoutAlong f g c S)).hom.hom.app U
          ((coefficientCarrierMap g c).hom.app U x))) := sorry

/-- Geometric algebra pullback respects the quotient, normalized base, and identified kernels. -/
theorem pullbackAlong_spec (S : AlgebraExtension (g.comp f) G) :
    Limits.pullback.fst S.proj (commRingStructureMap g) ≫ S.proj =
        (pullbackAlong f g S).proj ≫ commRingStructureMap g ∧
    (pullbackAlong f g S).structureMap ≫ Limits.pullback.fst S.proj (commRingStructureMap g) =
      (MorphismOfTopoiIn.commRingInverseImageCompIso f.toTopos g.toTopos OB).inv ≫ S.structureMap ∧
    (∀ U (x : G.val.obj U),
      (Limits.pullback.fst S.proj (commRingStructureMap g)).hom.app U
          (KernelIdeal.ιApp (pullbackAlong f g S).proj U
            ((kernelIso_forget (pullbackAlong f g S)).hom.hom.app U x)) =
        KernelIdeal.ιApp S.proj U ((kernelIso_forget S).hom.hom.app U x)) := sorry

/-- A lifted compatible morphism exists precisely when coefficient pushout and algebra
pullback have the same isomorphism class as extensions over their common base. -/
theorem exists_fittingMap_iff_isoClass (c : g.modulePullback.obj F ⟶ G)
    (S : AlgebraExtension f F) (T : AlgebraExtension (g.comp f) G) :
    (∃ φ : g.toTopos.commRingInverseImage.obj S.middle ⟶ T.middle, Fits f g c S T φ) ↔
      isoClassMk (pushoutAlong f g c S) = isoClassMk (pullbackAlong f g T) := sorry

/-- The pushout extension class is the canonical covariant image of the source extension class. -/
theorem pushoutAlong_extClass (c : g.modulePullback.obj F ⟶ G) (S : AlgebraExtension f F) :
    extOneRestrictEquiv f g G
      (Solution.extensionClass (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
        ((restrictionAlong (commRingStructureMap g)).obj G)
        (isoClassMk (pushoutAlong f g c S))) =
      NaiveCotangent.extOneMap f g c (extClass f S) := sorry

/-- The pullback extension class is the canonical cotangent-precomposition image of the
extension class over the composite morphism. -/
theorem pullbackAlong_extClass (S : AlgebraExtension (g.comp f) G) :
    extOneRestrictEquiv f g G
      (Solution.extensionClass (g.toTopos.commRingInverseImage.map (commRingStructureMap f))
        ((restrictionAlong (commRingStructureMap g)).obj G)
        (isoClassMk (pullbackAlong f g S))) =
      NaiveCotangent.extOneComap f g (extClass (g.comp f) S) := sorry

end RingedSite.ToposHom.AlgebraExtension
