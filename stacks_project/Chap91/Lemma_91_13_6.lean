/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.Lemma_91_13_1_Diagram
public import stacks_project.Chap91.Lemma_91_13_3
public import stacks_project.Chap91.Lemma_91_13_4
public import stacks_project.Chap91.Lemma_91_13_6_Map
public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.IsoClass
import StacksCheckRecall

public import ReasLib.AlgebraicGeometry.RingedSite.FirstOrderThickening.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.FirstOrderThickening.AlgebraExtension

@[expose] public section
open CategoryTheory
open RingedSite RingedSite.ToposHom
open scoped DerivedExt RingedSite.ToposHom
noncomputable section
universe u
-- Local instance justification (defeq pin): the naive cotangent Ext maps use the standard module derived category of the extension classification.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf spelling must select that same standard localization.
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
/- Lemma 91.13.6: compatible lifts of morphisms of ringed topoi are characterized by
 equality of the canonically transported extension classes. -/
@[stacks 0GQ7] #check (RingedSite.ToposHom.AlgebraExtension.fittingMap_exists_iff :
  ∀ (f : ToposHom (ofCommRingSheaf JC OC) (ofCommRingSheaf JB OB))
    (g : ToposHom (ofCommRingSheaf JD OD) (ofCommRingSheaf JC OC))
    [(SheafOfModules.restrictScalars.{u} g.structureMap).IsRightAdjoint]
    {F : ModuleCat.{u} (ofCommRingSheaf JC OC)}
    {G : ModuleCat.{u} (ofCommRingSheaf JD OD)} (c : g.modulePullback.obj F ⟶ G)
    (SC : AlgebraExtension f F) (SD : AlgebraExtension (g.comp f) G),
    (∃ φ : g.toTopos.commRingInverseImage.obj SC.middle ⟶ SD.middle,
      AlgebraExtension.Fits f g c SC SD φ) ↔
      NaiveCotangent.extOneMap f g c (AlgebraExtension.extClass f SC) =
        NaiveCotangent.extOneComap f g (AlgebraExtension.extClass (g.comp f) SD))
