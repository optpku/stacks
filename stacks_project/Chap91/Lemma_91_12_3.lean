/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Thickening.FlatMorphismSquare.Obstruction
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Abelian (Ext)
open SheafOfModules.RingedSite

noncomputable section

universe uC vC uB vB uC1 vC1 uC2 vC2 uB1 vB1 uB2 vB2 wExt

open RingedSite RingedSite.ToposHom RingedSite.ToposHom.Thickening
open RingedSite.ToposHom.Thickening.FlatMorphismSquare

variable {C : Type uC} [Category.{vC} C]
variable {B : Type uB} [Category.{vB} B]
variable {C1 : Type uC1} [Category.{vC1} C1]
variable {C2 : Type uC2} [Category.{vC2} C2]
variable {B1 : Type uB1} [Category.{vB1} B1]
variable {B2 : Type uB2} [Category.{vB2} B2]
variable {JC : GrothendieckTopology C}
variable {JB : GrothendieckTopology B}
variable {JC1 : GrothendieckTopology C1}
variable {JC2 : GrothendieckTopology C2}
variable {JB1 : GrothendieckTopology B1}
variable {JB2 : GrothendieckTopology B2}
variable [JC.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JB.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC1.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC2.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JB1.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JB2.HasSheafCompose (forget₂ CommRingCat.{max uC vC} RingCat.{max uC vC})]
variable [JC.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JB.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JC1.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JC2.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JB1.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JB2.HasSheafCompose (forget RingCat.{max uC vC})]
variable [JC.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JB.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JC1.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JC2.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JB1.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [JB2.HasSheafCompose (forget₂ RingCat.{max uC vC} AddCommGrpCat.{max uC vC})]
variable [HasSheafify JC1 AddCommGrpCat.{max uC vC}]
variable [JC1.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasSheafify JC2 AddCommGrpCat.{max uC vC}]
variable [JC2.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasSheafify JB1 AddCommGrpCat.{max uC vC}]
variable [JB1.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasSheafify JB2 AddCommGrpCat.{max uC vC}]
variable [JB2.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable [HasWeakSheafify JC AddCommGrpCat.{max uC vC}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{max uC vC}]
variable {O : Sheaf JC CommRingCat.{max uC vC}}
variable {O_B : Sheaf JB CommRingCat.{max uC vC}}
variable {O1' : Sheaf JC1 CommRingCat.{max uC vC}}
variable {O2' : Sheaf JC2 CommRingCat.{max uC vC}}
variable {OB1' : Sheaf JB1 CommRingCat.{max uC vC}}
variable {OB2' : Sheaf JB2 CommRingCat.{max uC vC}}


variable {f : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JB O_B)}
variable {i1 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC1 O1')}
variable {i2 : ToposHom (ofCommRingSheaf JC O) (ofCommRingSheaf JC2 O2')}
variable {t1 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB1 OB1')}
variable {t2 : ToposHom (ofCommRingSheaf JB O_B) (ofCommRingSheaf JB2 OB2')}
variable {f1' : ToposHom (ofCommRingSheaf JC1 O1') (ofCommRingSheaf JB1 OB1')}
variable {f2' : ToposHom (ofCommRingSheaf JC2 O2') (ofCommRingSheaf JB2 OB2')}
variable [IsFirstOrderThickening i1] [IsFirstOrderThickening i2]
variable [IsFirstOrderThickening t1] [IsFirstOrderThickening t2]
variable [(SheafOfModules.restrictScalars.{max uC vC} f1'.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} f2'.structureMap).IsRightAdjoint]


variable [(SheafOfModules.restrictScalars.{max uC vC} f.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} i1.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} i2.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} t1.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} t2.structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (i1.comp f1').structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (i2.comp f2').structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (f.comp t1).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars.{max uC vC} (f.comp t2).structureMap).IsRightAdjoint]

/- Lemma 91.12.3: in a coherent square of strict flat morphisms of first-order
thickenings, the canonical coefficient map sends the identity-infinitesimal
existence obstruction for the second thickening to that for the first. -/
@[stacks 0CYE] #check
  (RingedSite.ToposHom.Thickening.FlatMorphismSquare.obstruction_map :
    ∀ (S : FlatMorphismSquare f i1 i2 t1 t2 f1' f2')
      [(SheafOfModules.restrictScalars.{max uC vC} S.base.structureMap).IsRightAdjoint]
      [(SheafOfModules.restrictScalars.{max uC vC} (t1.comp S.base).structureMap).IsRightAdjoint]
      [(SheafOfModules.restrictScalars.{max uC vC} S.h.structureMap).IsRightAdjoint]
      [(SheafOfModules.restrictScalars.{max uC vC} (i1.comp S.h).structureMap).IsRightAdjoint]
      [HasWeakSheafify JC CommRingCat.{max uC vC}]
      [JC.WEqualsLocallyBijective CommRingCat.{max uC vC}]
      [HasSheafify JC AddCommGrpCat.{max uC vC}]
      [(SheafOfModules.restrictScalars (ringSheafMap (normalizedProjection i1))).IsRightAdjoint]
      [(SheafOfModules.restrictScalars (ringSheafMap (normalizedProjection i2))).IsRightAdjoint]
      [SheafOfModules.Localization.HasLowerShriek.{max uC vC}
        (ringSheaf JC (normalizedRing i1))]
      [SheafOfModules.Localization.HasLowerShriek.{max uC vC}
        (ringSheaf JC (normalizedRing i2))]
      [HasFunctorialInjectives
        (ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)]
      [HasExt.{wExt} (ringedSiteModuleCategory.{uC, vC, max uC vC, max uC vC} JC O)],
    (Ext.mk₀ (pullbackIdealTensorMap S)).postcomp S.module (add_zero 2)
        (existenceObstruction i2 S.module
          (moduleTensor (f.modulePullback.obj (idealModule t2)) S.module)
          (idealTensorIso_snd S).inv) =
      existenceObstruction i1 S.module
        (moduleTensor (f.modulePullback.obj (idealModule t1)) S.module)
        (idealTensorIso_fst S).inv)
